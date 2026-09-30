import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileCore
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! The ordinary Fourier integral of the actual Gaussian times an integer cusp phase. -/

noncomputable section
namespace GapFamily.Analytic.PoincareGammaGaussian
open MeasureTheory

/-- Multiplication by the actual unit Fourier phase preserves Gaussian integrability. -/
theorem integrable_gaussian_cuspFourierMode {u : ℝ} (hu : 0 < u) (j : ℤ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-(u : ℂ) * (t : ℂ) ^ 2) * cuspFourierMode (-j) t) := by
  have hm : AEStronglyMeasurable (fun t : ℝ =>
      Complex.exp (-(u : ℂ) * (t : ℂ) ^ 2) * cuspFourierMode (-j) t) volume := by
    apply Continuous.aestronglyMeasurable
    exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp (-(u : ℂ) * (t : ℂ) ^ 2))).mul
        (contDiff_cuspFourierMode (-j)).continuous
  apply (integrable_norm_iff hm).mp
  simpa only [norm_mul, norm_cuspFourierMode, mul_one] using
    (integrable_cexp_neg_mul_sq (show 0 < (u : ℂ).re from hu)).norm

/-- The literal integer-frequency Gaussian integral, with the positive-real
denominator power and its exact pi normalization. -/
theorem integral_gaussian_cuspFourierMode {u : ℝ} (hu : 0 < u) (j : ℤ) :
    (∫ t : ℝ, Complex.exp (-(u : ℂ) * (t : ℂ) ^ 2) * cuspFourierMode (-j) t) =
      (Real.sqrt Real.pi : ℂ) * (u : ℂ) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (-((Real.pi ^ 2 * (j : ℝ) ^ 2 : ℝ) : ℂ) / (u : ℂ)) := by
  have hphase (t : ℝ) :
      Complex.exp (Complex.I * (-2 * (Real.pi : ℂ) * (j : ℂ)) * (t : ℂ)) =
        cuspFourierMode (-j) t := by
    unfold cuspFourierMode
    congr 1
    push_cast
    ring
  have hfreq : -(-2 * (Real.pi : ℂ) * (j : ℂ)) ^ 2 / (4 * (u : ℂ)) =
      -((Real.pi ^ 2 * (j : ℝ) ^ 2 : ℝ) : ℂ) / (u : ℂ) := by
    push_cast
    field_simp
    ring
  have hpi : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  calc
    _ = ∫ t : ℝ, cuspFourierMode (-j) t *
        Complex.exp (-(u : ℂ) * (t : ℂ) ^ 2) := by
      apply integral_congr_ae
      exact ae_of_all volume (fun t => mul_comm _ _)
    _ = ((Real.pi : ℂ) / (u : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (-(-2 * (Real.pi : ℂ) * (j : ℂ)) ^ 2 / (4 * (u : ℂ))) := by
      simpa only [hphase] using
        fourierIntegral_gaussian (show 0 < (u : ℂ).re from hu)
          (-2 * (Real.pi : ℂ) * (j : ℂ))
    _ = _ := by
      rw [hfreq, Complex.div_cpow_ofReal_nonneg Real.pi_pos.le hu.le, hpi,
        Complex.cpow_neg, div_eq_mul_inv]

end GapFamily.Analytic.PoincareGammaGaussian
