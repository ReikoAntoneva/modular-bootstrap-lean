import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRemainderEstimate
import GapFamily.Analytic.Poincare.PoincareRemainderRadial

noncomputable section
namespace GapFamily.Analytic.PoincareFourierRemainder
open Set MeasureTheory

/-- Ordinary integrability uses the actual phase difference, for the full half-plane Re s>0. -/
theorem integrable_fourierRemainderKernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fourierRemainderKernel c y j J s) volume := by
  apply ((integrable_abs_mul_quadratic_rpow hy hs).const_mul
    (2 * Real.pi * |(J : ℝ)| * y ^ s.re * c ^ (-2 * s.re - 2))).mono'
      (continuous_fourierRemainderKernel hc hy j J s).aestronglyMeasurable
  filter_upwards with t
  exact norm_fourierRemainderKernel_le_radial hc hy j J s t

/-- Exact majorant mass; the c power includes the gain from input phase subtraction. -/
theorem integral_norm_fourierRemainderKernel_le {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ, ‖fourierRemainderKernel c y j J s t‖) ≤
      (2 * Real.pi * |(J : ℝ)| / s.re) * y ^ (-s.re) * c ^ (-2 * s.re - 2) := by
  calc
    (∫ t : ℝ, ‖fourierRemainderKernel c y j J s t‖) ≤
        ∫ t : ℝ, (2 * Real.pi * |(J : ℝ)| * y ^ s.re * c ^ (-2 * s.re - 2)) *
          (|t| * (t ^ 2 + y ^ 2) ^ (-s.re - 1)) := by
      exact integral_mono (integrable_fourierRemainderKernel hc hy j J hs).norm
        ((integrable_abs_mul_quadratic_rpow hy hs).const_mul _)
        (norm_fourierRemainderKernel_le_radial hc hy j J s)
    _ = _ := by
      rw [integral_const_mul, integral_abs_mul_quadratic_rpow hy hs]
      have hp : y ^ s.re * y ^ (-2 * s.re) = y ^ (-s.re) := by
        rw [← Real.rpow_add hy]
        congr 1
        ring
      calc
        (2 * Real.pi * |(J : ℝ)| * y ^ s.re * c ^ (-2 * s.re - 2)) *
            (y ^ (-2 * s.re) / s.re) =
          (2 * Real.pi * |(J : ℝ)| / s.re) *
            (y ^ s.re * y ^ (-2 * s.re)) * c ^ (-2 * s.re - 2) := by ring
        _ = _ := by rw [hp]

/-- The actual ordinary remainder integral has the same quantitative bound. -/
theorem norm_integral_fourierRemainderKernel_le {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t : ℝ, fourierRemainderKernel c y j J s t‖ ≤
      (2 * Real.pi * |(J : ℝ)| / s.re) * y ^ (-s.re) * c ^ (-2 * s.re - 2) :=
  (norm_integral_le_integral_norm _).trans (integral_norm_fourierRemainderKernel_le hc hy j J hs)

end GapFamily.Analytic.PoincareFourierRemainder
