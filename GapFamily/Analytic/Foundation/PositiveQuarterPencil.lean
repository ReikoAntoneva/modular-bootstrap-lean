import GapFamily.Analytic.Foundation.CompactSelfAdjointPencilRegular
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Regular parameters of a positive bounded response pencil

A positive response with norm at most four fifths gives an invertible pencil
outside the real ray starting at one quarter. The physical parameter
`z = 1 / 4 - κ ^ 2` lies in this regular set whenever `0 < κ.re`.
No compactness assumption is used.
-/

noncomputable section
namespace GapFamily.Analytic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive response of norm at most four fifths has no pencil singularity
outside the real quarter ray; compactness is not assumed. -/
theorem positiveQuarterPencil_bad_parameter (R : H →L[ℂ] H)
    (hR : R.IsPositive) (hnorm : ‖R‖ ≤ (4 / 5 : ℝ)) (z : ℂ)
    (hbad : ¬ IsUnit (1 - (z + 1) • R)) : z.im = 0 ∧ (1 / 4 : ℝ) ≤ z.re := by
  have hz : z ≠ -1 := by
    intro hz
    subst z
    simp only [neg_add_cancel, zero_smul, sub_zero] at hbad
    exact hbad isUnit_one
  have ha : z + 1 ≠ 0 := by simpa only [ne_eq, add_eq_zero_iff_eq_neg] using hz
  have hs : (z + 1)⁻¹ ∈ spectrum ℂ R := by
    by_contra hs
    exact hbad ((compactSelfAdjointPencil_isUnit_iff R hz).mpr hs)
  let μ : ℂ := (z + 1)⁻¹
  have hreal : μ = (μ.re : ℂ) := hR.isSelfAdjoint.mem_spectrum_eq_re hs
  have hμnonneg : 0 ≤ μ.re :=
    spectrum_nonneg_of_nonneg (ContinuousLinearMap.nonneg_iff_isPositive.mpr hR)
      (hR.isSelfAdjoint.spectrumRestricts.apply_mem hs)
  have hμbound : μ.re ≤ (4 / 5 : ℝ) := by
    calc
      μ.re ≤ ‖μ‖ := Complex.re_le_norm μ
      _ ≤ ‖R‖ * ‖(1 : H →L[ℂ] H)‖ := spectrum.norm_le_norm_mul_of_mem hs
      _ ≤ ‖R‖ := by
        change ‖R‖ * ‖ContinuousLinearMap.id ℂ H‖ ≤ ‖R‖
        exact (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := H)) (norm_nonneg R)).trans_eq
            (mul_one ‖R‖)
      _ ≤ 4 / 5 := hnorm
  have hproduct : (μ.re : ℂ) * (z + 1) = 1 := by
    rw [← hreal]
    exact inv_mul_cancel₀ ha
  have hre : μ.re * (z.re + 1) = 1 := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.add_re, Complex.one_re] using congrArg Complex.re hproduct
  have him : μ.re * z.im = 0 := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.add_im, Complex.one_im] using congrArg Complex.im hproduct
  have hμpos : 0 < μ.re := by
    by_contra h
    have hzero : μ.re = 0 := le_antisymm (le_of_not_gt h) hμnonneg
    simp only [hzero, zero_mul] at hre
    norm_num at hre
  refine ⟨(mul_eq_zero.mp him).resolve_left (ne_of_gt hμpos), ?_⟩
  have hzpos : 0 < z.re + 1 := by
    by_contra h
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hμpos.le (le_of_not_gt h)
    linarith
  have h1 : (1 : ℝ) ≤ (4 / 5) * (z.re + 1) := by
    calc
      1 = μ.re * (z.re + 1) := hre.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hμbound hzpos.le
  linarith

theorem positiveQuarterPencil_isUnit (R : H →L[ℂ] H)
    (hR : R.IsPositive) (hnorm : ‖R‖ ≤ (4 / 5 : ℝ)) {z : ℂ}
    (hz : z.im ≠ 0 ∨ z.re < (1 / 4 : ℝ)) : IsUnit (1 - (z + 1) • R) := by
  by_contra hbad
  obtain ⟨him, hre⟩ := positiveQuarterPencil_bad_parameter R hR hnorm z hbad
  exact hz.elim (fun h => h him) (fun h => (not_lt_of_ge hre) h)

theorem physicalQuarterParameter_regular {κ : ℂ} (hκ : 0 < κ.re) :
    ((1 / 4 : ℂ) - κ ^ 2).im ≠ 0 ∨ ((1 / 4 : ℂ) - κ ^ 2).re < (1 / 4 : ℝ) := by
  by_cases hi : κ.im = 0
  · right
    norm_num [Complex.sub_re, pow_two, Complex.mul_re, hi]
    nlinarith [sq_pos_of_pos hκ]
  · left
    have hproduct : 2 * κ.re * κ.im ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hκ)) hi
    intro h
    norm_num [Complex.sub_im, pow_two, Complex.mul_im] at h
    apply hproduct
    nlinarith

theorem positiveQuarterPencil_isUnit_physical (R : H →L[ℂ] H)
    (hR : R.IsPositive) (hnorm : ‖R‖ ≤ (4 / 5 : ℝ)) {κ : ℂ}
    (hκ : 0 < κ.re) : IsUnit (1 - (((1 / 4 : ℂ) - κ ^ 2) + 1) • R) :=
  positiveQuarterPencil_isUnit R hR hnorm (physicalQuarterParameter_regular hκ)

end GapFamily.Analytic
end
