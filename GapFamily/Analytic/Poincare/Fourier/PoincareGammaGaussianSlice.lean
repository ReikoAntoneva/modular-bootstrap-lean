import GapFamily.Analytic.Poincare.Fourier.PoincareGammaGaussianIntegrable
import GapFamily.Analytic.Poincare.Fourier.PoincareGaussianFourier

/-! Exact ordinary Gaussian evaluation of the fixed positive Gamma-parameter slice. -/

noncomputable section
namespace GapFamily.Analytic.PoincareGammaGaussian

open MeasureTheory

/-- Separate the fixed Gamma-parameter factor from the actual horizontal Gaussian. -/
theorem gammaFourierKernel_factor (y : ℝ) (j : ℤ) (s : ℂ) (t u : ℝ) :
    gammaFourierKernel y j s t u =
      ((u : ℂ) ^ (s - 1) * Complex.exp (-((y ^ 2 : ℝ) : ℂ) * (u : ℂ))) *
        (Complex.exp (-(u : ℂ) * (t : ℂ) ^ 2) * cuspFourierMode (-j) t) := by
  have harg : -((t ^ 2 + y ^ 2 : ℝ) : ℂ) * (u : ℂ) =
      -((y ^ 2 : ℝ) : ℂ) * (u : ℂ) + -(u : ℂ) * (t : ℂ) ^ 2 := by
    push_cast
    ring
  rw [gammaFourierKernel, harg, Complex.exp_add]
  ring

/-- Each positive-parameter slice is genuinely integrable in the horizontal variable. -/
theorem integrable_gammaFourierKernel_gaussian (y : ℝ) (j : ℤ) (s : ℂ)
    {u : ℝ} (hu : 0 < u) :
    Integrable (fun t : ℝ => gammaFourierKernel y j s t u) := by
  simp_rw [gammaFourierKernel_factor]
  exact (integrable_gaussian_cuspFourierMode hu j).const_mul _

/-- The actual Gaussian slice, with its exact positive-real power and pi normalization. -/
theorem integral_gammaFourierKernel_gaussian (y : ℝ) (j : ℤ) (s : ℂ)
    {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ, gammaFourierKernel y j s t u) =
      (Real.sqrt Real.pi : ℂ) * (u : ℂ) ^ (s - (3 / 2 : ℂ)) *
        Complex.exp (-((y ^ 2 : ℝ) : ℂ) * (u : ℂ) -
          ((Real.pi ^ 2 * (j : ℝ) ^ 2 : ℝ) : ℂ) / (u : ℂ)) := by
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hpow : (u : ℂ) ^ (s - 1) * (u : ℂ) ^ (-(1 / 2 : ℂ)) =
      (u : ℂ) ^ (s - (3 / 2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ hu0]
    congr 1
    ring
  simp_rw [gammaFourierKernel_factor]
  rw [integral_const_mul, integral_gaussian_cuspFourierMode hu j]
  calc
    _ = (Real.sqrt Real.pi : ℂ) *
        ((u : ℂ) ^ (s - 1) * (u : ℂ) ^ (-(1 / 2 : ℂ))) *
          (Complex.exp (-((y ^ 2 : ℝ) : ℂ) * (u : ℂ)) *
            Complex.exp (-((Real.pi ^ 2 * (j : ℝ) ^ 2 : ℝ) : ℂ) / (u : ℂ))) := by ring
    _ = _ := by
      rw [hpow, ← Complex.exp_add]
      congr 2
      ring

end GapFamily.Analytic.PoincareGammaGaussian
