import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.QuadraticDiscriminant

open MeasureTheory

namespace GapFamily.Analytic.SchurWeightedCauchy

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {k f : X → ℂ}

/-- The weighted first moment is genuinely integrable under the row mass and
weighted second-moment hypotheses. The measure need not be finite. -/
theorem integrable_weighted_norm
    (hk : AEStronglyMeasurable k μ) (hf : AEStronglyMeasurable f μ)
    (hrow : Integrable (fun y => ‖k y‖) μ)
    (hsecond : Integrable (fun y => ‖k y‖ * ‖f y‖ ^ 2) μ) :
    Integrable (fun y => ‖k y‖ * ‖f y‖) μ := by
  refine (hrow.fun_add hsecond).mono' (hk.norm.mul hf.norm) ?_
  filter_upwards [] with y
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have h : ‖f y‖ ≤ 1 + ‖f y‖ ^ 2 := by nlinarith [sq_nonneg (‖f y‖ - 1)]
  simpa only [mul_add, mul_one, Pi.add_apply] using
    mul_le_mul_of_nonneg_left h (norm_nonneg (k y))

/-- Genuine Bochner integrability of the complex kernel product. -/
theorem integrable_kernel_mul
    (hk : AEStronglyMeasurable k μ) (hf : AEStronglyMeasurable f μ)
    (hrow : Integrable (fun y => ‖k y‖) μ)
    (hsecond : Integrable (fun y => ‖k y‖ * ‖f y‖ ^ 2) μ) :
    Integrable (fun y => k y * f y) μ := by
  refine (integrable_weighted_norm hk hf hrow hsecond).mono' (hk.mul hf) ?_
  filter_upwards [] with y
  exact (norm_mul (k y) (f y)).le

/-- The rowwise Schur estimate from row mass and weighted second moment alone.
Its hypotheses also imply genuine integrability via `integrable_kernel_mul`. -/
theorem norm_integral_kernel_mul_sq_le
    (hk : AEStronglyMeasurable k μ) (hf : AEStronglyMeasurable f μ)
    (hrow : Integrable (fun y => ‖k y‖) μ)
    (hsecond : Integrable (fun y => ‖k y‖ * ‖f y‖ ^ 2) μ) :
    ‖∫ y, k y * f y ∂μ‖ ^ 2 ≤
      (∫ y, ‖k y‖ ∂μ) * (∫ y, ‖k y‖ * ‖f y‖ ^ 2 ∂μ) := by
  have hfirst := integrable_weighted_norm hk hf hrow hsecond
  have hquadratic (t : ℝ) :
      0 ≤ (∫ y, ‖k y‖ ∂μ) * (t * t) +
        (2 * ∫ y, ‖k y‖ * ‖f y‖ ∂μ) * t +
        ∫ y, ‖k y‖ * ‖f y‖ ^ 2 ∂μ := by
    have hnonneg : 0 ≤ ∫ y, ‖k y‖ * (t + ‖f y‖) ^ 2 ∂μ :=
      integral_nonneg fun y => mul_nonneg (norm_nonneg _) (sq_nonneg _)
    have heq : (fun y => ‖k y‖ * (t + ‖f y‖) ^ 2) =
        (fun y => (t * t) * ‖k y‖ + (2 * t) * (‖k y‖ * ‖f y‖) +
          ‖k y‖ * ‖f y‖ ^ 2) := by
      funext y
      ring
    have hsum : Integrable
        (fun y => (t * t) * ‖k y‖ + (2 * t) * (‖k y‖ * ‖f y‖)) μ := by
      exact (hrow.const_mul (t * t)).fun_add (hfirst.const_mul (2 * t))
    rw [heq, integral_add hsum hsecond,
      integral_add (hrow.const_mul _) (hfirst.const_mul _),
      integral_const_mul, integral_const_mul] at hnonneg
    nlinarith only [hnonneg]
  have hdiscriminant := discrim_le_zero hquadratic
  rw [discrim] at hdiscriminant
  have hnorm : ‖∫ y, k y * f y ∂μ‖ ≤ ∫ y, ‖k y‖ * ‖f y‖ ∂μ := by
    simpa only [norm_mul] using norm_integral_le_integral_norm (fun y => k y * f y)
  have hfirst_nonneg : 0 ≤ ∫ y, ‖k y‖ * ‖f y‖ ∂μ :=
    integral_nonneg fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (∫ y, k y * f y ∂μ)]

end GapFamily.Analytic.SchurWeightedCauchy
