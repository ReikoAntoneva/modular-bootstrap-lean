import BTZEntropy.Analytic.IntegerReferenceInversion
import BTZEntropy.Comparison.SpinComplexEstimate
import BTZEntropy.Comparison.SpinErrorScale
import BTZEntropy.Comparison.SpinContourBound
import BTZEntropy.Analytic.KernelContourUniform

/-! The integer-spin reference and the actual continuous BTZ count. -/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- The finite charge shift leaves a favorable term in the exact saddle exponent. -/
theorem spinReferenceExponent_le_leadingAction {x : ℝ} (hx : 0 < x) (a : ℝ) :
    saddleBeta x * (x * (12 * a + 1)) + 4 * Real.pi ^ 2 * a / saddleBeta x ≤
      leadingAction x (12 * a + 1) := by
  have hβ := saddleBeta_pos hx
  have hphase := saddlePhase_at_saddle hx
  have heq : leadingAction x (12 * a + 1) =
      saddleBeta x * (x * (12 * a + 1)) + 4 * Real.pi ^ 2 * a / saddleBeta x +
        phaseConstant / saddleBeta x := by
    calc
      _ = (12 * a + 1) * saddlePhase x (saddleBeta x) := by
        rw [hphase]
        unfold leadingAction
        ring
      _ = _ := by
        unfold saddlePhase phaseConstant
        ring
  rw [heq]
  exact le_add_of_nonneg_right (div_nonneg phaseConstant_pos.le hβ.le)

private theorem spinComparison_exp_bound_of_kernel (φ : SmoothKernel)
    {L U M : ℝ} (hL : 0 < L) (hLU : L ≤ U) (hM : 0 < M)
    (hkernel : ∀ β ∈ Set.Icc (saddleBeta U) (saddleBeta L),
      (∫ t : ℝ, ‖complexKernelTransform φ (saddleContour β t)‖) ≤ M) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧ ∀ a : ℝ, 2 ≤ a → ∀ x ∈ Set.Icc L U,
      |Comparison.integerLeadingSmoothCount φ a 0 (x * (12 * a + 1)) -
        btzCount φ x (12 * a + 1)| ≤
          C * Real.exp (leadingAction x (12 * a + 1)) * Real.exp (-d * a) := by
  obtain ⟨C, d, hC, hd, hbound⟩ := fullSpinCorrectionContour_uniform_bound φ
    (saddleBeta_pos (hL.trans_le hLU)) (saddleBeta_antitone hL hLU)
  refine ⟨C * M, d, mul_pos hC hM, hd, ?_⟩
  intro a ha x hx
  have hx0 : 0 < x := hL.trans_le hx.1
  have hβ := saddleBeta_mem_Icc hL hx
  have h := hbound a ha (saddleBeta x) hβ (x * (12 * a + 1))
  push_cast at h
  rw [← integerLeadingSmoothCount_sub_btz_eq_contour φ ha hx0 (saddleBeta_pos hx0),
    Complex.norm_real, Real.norm_eq_abs] at h
  calc
    _ ≤ _ := h
    _ ≤ C * Real.exp (leadingAction x (12 * a + 1)) * Real.exp (-d * a) * M := by
      gcongr
      · exact spinReferenceExponent_le_leadingAction hx0 a
      · exact hkernel _ hβ
    _ = _ := by ring

/-- The actual full-cone integer-spin and continuous BTZ counts have a uniform
strict exponential gap on each positive compact energy-ratio interval. -/
theorem integerLeadingSmoothCount_sub_btz_exp_bound (φ : SmoothKernel)
    {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧ ∀ a : ℝ, 2 ≤ a → ∀ x ∈ Set.Icc L U,
      |Comparison.integerLeadingSmoothCount φ a 0 (x * (12 * a + 1)) -
        btzCount φ x (12 * a + 1)| ≤
          C * Real.exp (leadingAction x (12 * a + 1)) * Real.exp (-d * a) := by
  obtain ⟨M, hM, hkernel⟩ := exists_pos_bound_integral_norm_complexKernelTransform φ
    (saddleBeta U) (saddleBeta L)
  exact spinComparison_exp_bound_of_kernel φ hL hLU hM hkernel

/-- The complete integer-spin reference has the same all-order saddle expansion
as the actual continuous BTZ count. Both descendant towers are included. -/
theorem integerLeadingSmoothCount_sub_btz_saddleScale (φ : SmoothKernel)
    {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) (q : ℕ) :
    ∃ A : ℝ, 2 ≤ A ∧ ∀ a, A ≤ a → ∀ x ∈ Set.Icc L U,
      |(Comparison.integerLeadingSmoothCount φ a 0 (x * (12 * a + 1)) -
        btzCount φ x (12 * a + 1)) / saddleCountScale φ x (12 * a + 1)| ≤
          1 / (12 * a + 1) ^ q := by
  obtain ⟨C, d, hC, hd, herr⟩ := integerLeadingSmoothCount_sub_btz_exp_bound φ hL hLU
  exact exists_normalized_exponential_error_threshold φ hL hLU hC hd
    (fun a x => Comparison.integerLeadingSmoothCount φ a 0 (x * (12 * a + 1)) -
      btzCount φ x (12 * a + 1)) herr q

end BTZEntropy
