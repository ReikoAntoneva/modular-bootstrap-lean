import GapFamily.Analytic.Poincare.PoincareHighCuspLift

/-!
A common finite expansion of the actual high-cusp periodization on every
compact observation set, independent of the Fourier index and exponent.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareHighCuspAnalytic

open Set UpperHalfPlane PoincareHighCusp
open scoped Topology MatrixGroups ComplexOrder

/-- Proper discontinuity gives one finite collection of actual modular terms
for every Fourier index and exponent on a fixed compact observation set. -/
theorem exists_finset_highCuspLift_eq_on_compact {K : Set UpperHalfPlane}
    (hK : IsCompact K) :
    ∃ Γ : Finset SL(2, ℤ), ∀ (J : ℤ) (s : ℂ) (τ : UpperHalfPlane), τ ∈ K →
      highCuspLift J s (τ : ℂ) = (1 / 2 : ℂ) *
        ∑ γ ∈ Γ, cuspFourierProfileSeed J (highProfile s) (↑(γ • τ : UpperHalfPlane) : ℂ) := by
  classical
  obtain ⟨H, hH⟩ := exists_bound_modular_smul_im_of_isCompact hK
  let D : Set ℂ := (Icc (-1 / 2 : ℝ) (3 / 2)) ×ℂ Icc (1 : ℝ) H
  have hD : IsCompact D := isCompact_Icc.reProdIm isCompact_Icc
  have hDU : D ⊆ upperHalfPlaneSet := by
    intro w hw
    exact lt_of_lt_of_le zero_lt_one hw.2.1
  let D' : Set UpperHalfPlane := UpperHalfPlane.coe ⁻¹' D
  have hD' : IsCompact D' := by
    apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
    change IsCompact (UpperHalfPlane.coe '' (UpperHalfPlane.coe ⁻¹' D))
    rw [Set.image_preimage_eq_inter_range, UpperHalfPlane.range_coe,
      Set.inter_eq_left.mpr hDU]
    exact hD
  let A : Set SL(2, ℤ) := {γ | ((γ • ·) '' K ∩ D').Nonempty}
  have hA : A.Finite := ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK hD'
  refine ⟨hA.toFinset, ?_⟩
  intro J s τ hτ
  rw [highCuspLift, modularPeriodization_coe]
  congr 1
  apply tsum_eq_sum
  intro γ hγ
  by_contra hseed
  have hbase : cuspProfileSeed (highProfile s) (↑(γ • τ : UpperHalfPlane) : ℂ) ≠ 0 := by
    intro h
    exact hseed (by simp only [cuspFourierProfileSeed, h, zero_mul])
  have hmul : (cuspTranslationWeight (γ • τ : UpperHalfPlane).re : ℂ) *
      highProfile s (γ • τ : UpperHalfPlane).im ≠ 0 := hbase
  have hp := mul_ne_zero_iff.mp hmul
  have hx : (γ • τ : UpperHalfPlane).re ∈ Icc (-1 / 2 : ℝ) (3 / 2) := by
    apply cuspTranslationWeight_tsupport_subset
    apply subset_tsupport cuspTranslationWeight
    exact fun h => hp.1 (by simp only [h, Complex.ofReal_zero])
  have hy : 1 < (γ • τ : UpperHalfPlane).im :=
    tsupport_highProfile_upper s (subset_tsupport (highProfile s) hp.2)
  have hmem : (γ • τ : UpperHalfPlane) ∈ D' := ⟨hx, hy.le, hH τ hτ γ⟩
  exact hγ (hA.mem_toFinset.mpr ⟨γ • τ, ⟨τ, hτ, rfl⟩, hmem⟩)

end GapFamily.Analytic.PoincareHighCuspAnalytic
