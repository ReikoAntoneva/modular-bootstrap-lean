import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRemainderKernel

noncomputable section
namespace GapFamily.Analytic.PoincareFourierRemainder
open Set MeasureTheory

/-- Exact factorization of the positive radial majorant. -/
theorem fourierRemainder_majorant_factor {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (J : ℤ) (σ t : ℝ) :
    (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ σ *
        (2 * Real.pi * |(J : ℝ)| * (|t| / (c ^ 2 * (t ^ 2 + y ^ 2)))) =
      (2 * Real.pi * |(J : ℝ)| * y ^ σ * c ^ (-2 * σ - 2)) *
        (|t| * (t ^ 2 + y ^ 2) ^ (-σ - 1)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hq : 0 < t ^ 2 + y ^ 2 := by positivity
  rw [Real.div_rpow hy.le (mul_pos hc2 hq).le, Real.mul_rpow hc2.le hq.le]
  have he : c ^ (-2 * σ - 2) = (c ^ 2) ^ (-σ - 1) := by
    rw [show -2 * σ - 2 = (2 : ℕ) * (-σ - 1) by push_cast; ring,
      Real.rpow_natCast_mul hc.le]
  rw [he, Real.rpow_sub_one hc2.ne', Real.rpow_sub_one hq.ne',
    Real.rpow_neg hc2.le, Real.rpow_neg hq.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The precise pointwise radial estimate, uniform in the output spin. -/
theorem norm_fourierRemainderKernel_le_radial {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) (s : ℂ) (t : ℝ) :
    ‖fourierRemainderKernel c y j J s t‖ ≤
      (2 * Real.pi * |(J : ℝ)| * y ^ s.re * c ^ (-2 * s.re - 2)) *
        (|t| * (t ^ 2 + y ^ 2) ^ (-s.re - 1)) := by
  simpa only [fourierRemainder_majorant_factor hc hy J s.re t] using
    norm_fourierRemainderKernel_le hc hy j J s t

end GapFamily.Analytic.PoincareFourierRemainder
