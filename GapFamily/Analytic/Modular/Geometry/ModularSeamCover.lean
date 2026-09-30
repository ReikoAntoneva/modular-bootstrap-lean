/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

The proof of `modular_smul_im_le_max` is adapted from the final height estimate
in `ModularGroup.exists_bound_of_invariant_of_isBigO`, in
Mathlib/NumberTheory/ModularForms/Bounds.lean at mathlib commit
5ed2965256430c3649e86755f9576b54eca72435. The original notice above applies to
that adapted proof; LICENSE refers to the pinned mathlib license:
https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/LICENSE

The adaptation extracts the estimate as a standalone lemma and names its
intermediate bounds. The compact-cover proofs below are project additions.
-/

import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationLocal
import Mathlib.NumberTheory.Modular

/-!
# Finite closed-fundamental-domain cover of a compact set

A compact set in the upper half-plane meets only finitely many translates of
a sufficiently high compact truncation of the closed modular fundamental
domain. The closed domain includes its seams, so the cover loses no points.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Matrix UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Pointwise

/-- Every modular translate has height bounded in terms of the original height.
The proof extracts the height estimate in mathlib's
`ModularGroup.exists_bound_of_invariant_of_isBigO`, using integer lower
bounds for the bottom matrix row. -/
theorem modular_smul_im_le_max (g : SL(2, ℤ)) (τ : ℍ) :
    (g • τ).im ≤ max τ.im (1 / τ.im) := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  by_cases hg : g 1 0 = 0
  · have hd : g 1 1 ≠ 0 := fun hg' ↦ zero_ne_one <| by
      simpa only [Matrix.det_fin_two, hg, hg', mul_zero, sub_zero] using g.det_coe
    have hd2 : (1 : ℝ) ≤ g 1 1 ^ 2 :=
      mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hd)
    refine le_trans ?_ (le_max_left _ _)
    rw [show Complex.normSq ((g 1 0) * τ + (g 1 1)) = (g 1 1) ^ 2 by
      simp [hg, sq]]
    simpa [field] using inv_le_one_of_one_le₀ hd2
  · refine le_trans ?_ (le_max_right _ _)
    rw [show 1 / τ.im = τ.im / τ.im ^ 2 by field_simp]
    gcongr
    rw [show Complex.normSq ((g 1 0) * τ + (g 1 1)) =
      ((g 1 0) * τ.re + (g 1 1)) ^ 2 + (g 1 0) ^ 2 * τ.im ^ 2 by
      simp [Complex.normSq_apply]; ring]
    have hc2 : (1 : ℝ) ≤ g 1 0 ^ 2 :=
      mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hg)
    nlinarith

/-- On a compact set, the heights of all modular translates admit one bound. -/
theorem exists_bound_modular_smul_im_of_isCompact {K : Set ℍ} (hK : IsCompact K) :
    ∃ H : ℝ, ∀ τ ∈ K, ∀ g : SL(2, ℤ), (g • τ).im ≤ H := by
  have hc : Continuous (fun τ : ℍ => max τ.im (1 / τ.im)) :=
    UpperHalfPlane.continuous_im.max
      (continuous_const.div UpperHalfPlane.continuous_im (fun τ => τ.im_ne_zero))
  obtain ⟨H, hH⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨H, fun τ hτ g => ?_⟩
  exact (modular_smul_im_le_max g τ).trans
    ((le_abs_self _).trans (hH τ hτ))

/-- A compact subset of the upper half-plane is covered by finitely many
translates of one compact truncation of the closed fundamental domain. -/
theorem exists_finite_modular_truncated_cover {K : Set ℍ} (hK : IsCompact K) :
    ∃ H : ℝ, ∃ Γ : Finset SL(2, ℤ),
      K ⊆ ⋃ γ ∈ Γ, (γ • ·) '' ModularGroup.truncatedFundamentalDomain H := by
  classical
  obtain ⟨H, hH⟩ := exists_bound_modular_smul_im_of_isCompact hK
  let C := ModularGroup.truncatedFundamentalDomain H
  have hC : IsCompact C := ModularGroup.isCompact_truncatedFundamentalDomain H
  let S : Set SL(2, ℤ) := {γ | ((γ • ·) '' C ∩ K).Nonempty}
  have hS : S.Finite := ProperlyDiscontinuousSMul.finite_disjoint_inter_image hC hK
  refine ⟨H, hS.toFinset, fun τ hτ => ?_⟩
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  have hgC : g • τ ∈ C := ⟨hg, hH τ hτ g⟩
  have hτimage : τ ∈ (g⁻¹ • ·) '' C := ⟨g • τ, hgC, inv_smul_smul g τ⟩
  have hginv : g⁻¹ ∈ hS.toFinset := hS.mem_toFinset.mpr ⟨τ, hτimage, hτ⟩
  exact Set.mem_iUnion.mpr ⟨g⁻¹, Set.mem_iUnion.mpr ⟨hginv, hτimage⟩⟩

/-- A genuine finite cover by translates of the closed fundamental domain,
including all side and circular seams. -/
theorem exists_finite_modular_fd_cover {K : Set ℍ} (hK : IsCompact K) :
    ∃ Γ : Finset SL(2, ℤ), K ⊆ ⋃ γ ∈ Γ, (γ • ·) '' ModularGroup.fd := by
  obtain ⟨H, Γ, hΓ⟩ := exists_finite_modular_truncated_cover hK
  refine ⟨Γ, hΓ.trans ?_⟩
  apply Set.iUnion_mono
  intro γ
  apply Set.iUnion_mono
  intro hγ
  exact Set.image_mono (fun τ hτ => hτ.1)

end GapFamily.Analytic
