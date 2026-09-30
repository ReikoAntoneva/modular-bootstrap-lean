import BTZEntropy.Comparison.SpinComplexEstimate
import BTZEntropy.Analytic.ReferenceInversionKernel

/-!
# Absolute bound for the full spin correction contour

The exact descendant and cylinder factors remain inside the same inverse
contour as the physical reference comparison. The uniform pointwise spin loss
and the genuine kernel L¹ norm give its absolute integral bound.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- A compact strip has one exponential-loss estimate for the entire actual
spin correction contour, for every real observed energy. -/
theorem fullSpinCorrectionContour_uniform_bound (φ : SmoothKernel) {βmin βmax : ℝ}
    (hmin : 0 < βmin) (hmax : βmin ≤ βmax) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧ ∀ a : ℝ, 2 ≤ a →
      ∀ β ∈ Set.Icc βmin βmax, ∀ E : ℝ,
        ‖(1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
          Complex.exp (saddleContour β t * E) * complexKernelTransform φ (saddleContour β t) *
            (Complex.exp (saddleContour β t / 12) *
              (complexEulerProduct (Complex.exp (-saddleContour β t)))⁻¹ ^ 2 *
                (integerSpinPrimaryComplexTransform a (saddleContour β t) -
                  complexReferencePrimaryTransform a (saddleContour β t)))‖ ≤
          C * Real.exp (β * E + 4 * Real.pi ^ 2 * a / β) * Real.exp (-d * a) *
            ∫ t : ℝ, ‖complexKernelTransform φ (saddleContour β t)‖ := by
  obtain ⟨C, d, hC, hd, hbound⟩ := fullSpinCorrection_uniform_bound hmin hmax
  refine ⟨C / (2 * Real.pi), d, div_pos hC (by positivity), hd, ?_⟩
  intro a ha β hβ E
  let A := Real.exp (β * E) * (C * Real.exp (4 * Real.pi ^ 2 * a / β) * Real.exp (-d * a))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK := (integrable_complexKernelTransform_contour φ β).norm
  have hpoint (t : ℝ) :
      ‖Complex.exp (saddleContour β t * E) * complexKernelTransform φ (saddleContour β t) *
          (Complex.exp (saddleContour β t / 12) *
            (complexEulerProduct (Complex.exp (-saddleContour β t)))⁻¹ ^ 2 *
              (integerSpinPrimaryComplexTransform a (saddleContour β t) -
                complexReferencePrimaryTransform a (saddleContour β t)))‖ ≤
        A * ‖complexKernelTransform φ (saddleContour β t)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre : (saddleContour β t * (E : ℂ)).re = β * E := by simp
    rw [hre]
    calc
      _ ≤ (Real.exp (β * E) * ‖complexKernelTransform φ (saddleContour β t)‖) *
          (C * Real.exp (4 * Real.pi ^ 2 * a / β) * Real.exp (-d * a)) :=
        mul_le_mul_of_nonneg_left (hbound a ha β hβ t) (by positivity)
      _ = _ := by dsimp [A]; ring
  have hint := norm_integral_le_of_norm_le (hK.const_mul A)
    (Filter.Eventually.of_forall hpoint)
  have hnorm : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    norm_num [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [norm_mul, hnorm]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        (∫ t : ℝ, A * ‖complexKernelTransform φ (saddleContour β t)‖) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by
      rw [integral_const_mul, Real.exp_add]
      dsimp [A]
      ring

end BTZEntropy
