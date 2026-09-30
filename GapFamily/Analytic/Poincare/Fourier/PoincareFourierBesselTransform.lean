import GapFamily.Analytic.Poincare.Fourier.PoincareGammaGaussianTransform
import GapFamily.Analytic.Bessel.BesselMellinTransform
import GapFamily.Analytic.Bessel.BesselFourierNormalization
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierCentralPower

noncomputable section
namespace GapFamily.Analytic.PoincareFourierRemainder
open MeasureTheory Set BesselCoshOrder

/-- The literal central Fourier transform equals the complex-order Bessel expression.
All integrals in the proof are ordinary and genuinely integrable for Re(s)>1/2. -/
theorem integral_centralFourierKernel_eq_besselK {y : ℝ} (hy : 0 < y)
    {j : ℤ} (hj : j ≠ 0) {s : ℂ} (hs : 1 / 2 < s.re) :
    (∫ t : ℝ, centralFourierKernel y j s t) =
      2 * (Real.pi : ℂ) ^ s / Complex.Gamma s *
        ((|(j : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * (Real.sqrt y : ℂ) *
          besselK (s - 1 / 2) (2 * Real.pi * |(j : ℝ)| * y) := by
  have hjn : (j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hj
  have hn : 0 < |(j : ℝ)| := abs_pos.mpr hjn
  have ha : 0 < y ^ 2 := sq_pos_of_pos hy
  have hb : 0 < Real.pi ^ 2 * (j : ℝ) ^ 2 :=
    mul_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_ne_zero hjn)
  have hm : (∫ u : ℝ in Ioi 0, (u : ℂ) ^ (s - (3 / 2 : ℂ)) *
      Complex.exp (-((y ^ 2 : ℝ) : ℂ) * (u : ℂ) -
        ((Real.pi ^ 2 * (j : ℝ) ^ 2 : ℝ) : ℂ) / (u : ℂ))) =
      2 * (Real.sqrt ((Real.pi ^ 2 * (j : ℝ) ^ 2) / y ^ 2) : ℂ) ^ (s - 1 / 2) *
        besselK (s - 1 / 2) (2 * Real.sqrt (y ^ 2 * (Real.pi ^ 2 * (j : ℝ) ^ 2))) := by
    have he : s - (3 / 2 : ℂ) = (s - 1 / 2) - 1 := by ring
    simpa only [mellinIntegrand, he] using integral_mellinIntegrand (s - 1 / 2) ha hb
  rw [PoincareGammaGaussian.integral_centralFourierKernel_eq_mellin hy j hs, hm]
  rw [← sq_abs (j : ℝ), sqrt_fourier_argument hy hn]
  have harg : 2 * (Real.pi * |(j : ℝ)| * y) = 2 * Real.pi * |(j : ℝ)| * y := by ring
  rw [harg]
  rw [← mul_assoc, fourier_mellin_prefactor s (Complex.Gamma s) hy hn]

/-- The source's exterior-height normalization of the ordinary rational Fourier integral. -/
theorem height_mul_integral_rationalFourierKernel_eq_besselK {y : ℝ} (hy : 0 < y)
    {j : ℤ} (hj : j ≠ 0) {s : ℂ} (hs : 1 / 2 < s.re) :
    (y : ℂ) ^ s *
      (∫ t : ℝ, (((t ^ 2 + y ^ 2 : ℝ) : ℂ) ^ (-s)) * cuspFourierMode (-j) t) =
      2 * (Real.pi : ℂ) ^ s / Complex.Gamma s *
        ((|(j : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * (Real.sqrt y : ℂ) *
          besselK (s - 1 / 2) (2 * Real.pi * |(j : ℝ)| * y) := by
  rw [← integral_centralFourierKernel_eq_height_mul hy j s]
  exact integral_centralFourierKernel_eq_besselK hy hj hs

end GapFamily.Analytic.PoincareFourierRemainder
