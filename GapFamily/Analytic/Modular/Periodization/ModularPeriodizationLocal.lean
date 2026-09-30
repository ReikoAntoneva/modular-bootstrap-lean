import GapFamily.Analytic.Modular.Geometry.ModularCoordinate
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Local finiteness for actual modular periodization

The integer matrix group itself acts properly discontinuously, including its
finite central kernel. Compactly supported interior functions therefore have
genuinely finite orbit sums in a neighborhood of every upper-half-plane point.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane Pointwise

instance modularGroup_properlyDiscontinuous : ProperlyDiscontinuousSMul SL(2, ℤ) ℍ := by
  constructor
  intro K L hK hL
  have hf := (Subgroup.properlyDiscontinuousSMul_iff 𝒮ℒ).mp
    (inferInstance : ProperlyDiscontinuousSMul 𝒮ℒ ℍ) hK hL
  have hp := hf.preimage (mapGL_injective (R := ℤ) (S := ℝ)).injOn
  exact hp.subset (fun γ hγ => ⟨⟨γ, rfl⟩, hγ⟩)

/-- Images of a compact set form a locally finite family under the full matrix group. -/
theorem locallyFinite_modular_translate {K : Set ℍ} (hK : IsCompact K) :
    LocallyFinite (fun γ : SL(2, ℤ) => (γ • ·) '' K) := by
  intro τ
  obtain ⟨L, hL, hLτ⟩ := exists_compact_mem_nhds τ
  exact ⟨L, hLτ, ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK hL⟩

/-- Pullback translates of a compact set are locally finite as well. -/
theorem locallyFinite_modular_preimage {K : Set ℍ} (hK : IsCompact K) :
    LocallyFinite (fun γ : SL(2, ℤ) => (γ • ·) ⁻¹' K) := by
  have h := (locallyFinite_modular_translate hK).comp_injective
    (inv_injective : Function.Injective (Inv.inv : SL(2, ℤ) → SL(2, ℤ)))
  convert h using 1
  funext γ
  ext τ
  constructor
  · intro hτ
    exact ⟨γ • τ, hτ, inv_smul_smul γ τ⟩
  · rintro ⟨w, hw, rfl⟩
    simpa only [Set.mem_preimage, smul_inv_smul] using hw

/-- A compact complex support inside the open domain remains compact in `ℍ`. -/
theorem compact_modular_support_preimage {φ : ℂ → ℂ} (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) :
    IsCompact (UpperHalfPlane.coe ⁻¹' tsupport φ) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr
    (hs.trans (Set.image_subset_range _ _))]
  exact hc

theorem locallyFinite_modular_orbit_support {φ : ℂ → ℂ} (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) :
    LocallyFinite (fun γ : SL(2, ℤ) =>
      Function.support (fun τ : ℍ => φ (↑(γ • τ : ℍ) : ℂ))) := by
  apply (locallyFinite_modular_preimage (compact_modular_support_preimage hc hs)).subset
  intro γ τ hτ
  exact subset_tsupport _ hτ

end GapFamily.Analytic
