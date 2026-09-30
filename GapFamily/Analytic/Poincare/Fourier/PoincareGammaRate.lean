import GapFamily.Analytic.Poincare.Fourier.PoincareFourierCentralFactor
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

noncomputable section
namespace GapFamily.Analytic.PoincareGammaGaussian
open Set MeasureTheory PoincareFourierRemainder

/-- The exact Gamma representation of the literal central kernel, pointwise in
its real Fourier coordinate. The scale has positive real rate t²+y². -/
theorem gamma_mul_centralFourierKernel_eq {y : ℝ} (hy : 0 < y) (j : ℤ)
    {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    Complex.Gamma s * centralFourierKernel y j s t =
      (y : ℂ) ^ s * ∫ u : ℝ in Ioi 0,
        (u : ℂ) ^ (s - 1) * Complex.exp (-((t ^ 2 + y ^ 2 : ℝ) : ℂ) * (u : ℂ)) *
          cuspFourierMode (-j) t := by
  have hq : 0 < t ^ 2 + y ^ 2 := by positivity
  have hG : (∫ u : ℝ in Ioi 0,
      (u : ℂ) ^ (s - 1) * Complex.exp (-((t ^ 2 + y ^ 2 : ℝ) : ℂ) * (u : ℂ))) =
      (1 / ((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ s * Complex.Gamma s := by
    simpa only [neg_mul] using
      (Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := s) hs hq)
  rw [integral_mul_const, hG]
  have hp : (y : ℂ) ^ s * (1 / ((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ s =
      ((y / (t ^ 2 + y ^ 2) : ℝ) : ℂ) ^ s := by
    have hh := Complex.mul_cpow_ofReal_nonneg hy.le
      (show 0 ≤ 1 / (t ^ 2 + y ^ 2) by positivity) s
    simpa only [Complex.ofReal_div, Complex.ofReal_one, mul_one_div] using hh.symm
  unfold centralFourierKernel
  rw [← hp]
  ring

end GapFamily.Analytic.PoincareGammaGaussian
