import GapFamily.Analytic.Spatial.SpatialPointFourierLaplaceBasic
import GapFamily.Analytic.Spatial.SpatialPointConeContinuity
import GapFamily.Analytic.Spatial.SpatialPointConeIntegrable
import GapFamily.Analytic.Foundation.FourierDouble

/-! Ordinary continuous frequency density and its literal Fourier phases.
These statements use no spatial Fourier transform identity. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set MeasureTheory PoincareFourier
open scoped FourierTransform

/-- The positive-phase density whose Fourier transform is the point kernel. -/
def pointFrequencyDensity (s : ℂ) (y : ℝ) (w : UpperHalfPlane) (J : ℝ) : ℂ :=
  spatialLaplaceConstantComplex s * ((y * w.im : ℝ) : ℂ) ^ s *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (w.re : ℂ) * (J : ℂ)) *
      ∫ E : ℝ in Ioi |J|, pointFourierLaplaceDensity s (y + w.im) J E

theorem continuous_pointFrequencyDensity (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) :
    Continuous (pointFrequencyDensity s y w) := by
  have hD := continuous_pointConeFrequencyIntegral s hs (y + w.im) (add_pos hy w.im_pos)
  exact (continuous_const.mul (by fun_prop)).mul hD

theorem integrable_pointFrequencyDensity (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) :
    Integrable (pointFrequencyDensity s y w) := by
  change Integrable (fun J => pointFrequencyDensity s y w J)
  have hD : Integrable (fun J : ℝ =>
      ∫ E : ℝ in Ioi |J|, pointFourierLaplaceDensity s (y + w.im) J E) :=
    integrable_complexPointConeDensity_frequency hs (add_pos hy w.im_pos)
  have hi := hD.bdd_mul (c := 1)
    (by fun_prop : Continuous (fun J : ℝ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (w.re : ℂ) * (J : ℂ)))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun J => by
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im])
  simpa only [pointFrequencyDensity, mul_assoc] using
    hi.const_mul (spatialLaplaceConstantComplex s * ((y * w.im : ℝ) : ℂ) ^ s)

theorem pointFrequencyDensity_neg (s : ℂ) (y : ℝ) (w : UpperHalfPlane) (J : ℝ) :
    pointFrequencyDensity s y w (-J) =
      spatialLaplaceConstantComplex s * ((y * w.im : ℝ) : ℂ) ^ s *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (w.re : ℂ)) *
          ∫ E : ℝ in Ioi |J|, pointFourierLaplaceDensity s (y + w.im) J E := by
  simp only [pointFrequencyDensity, abs_neg, pointFourierLaplaceDensity, neg_sq,
    Complex.ofReal_neg]
  congr 2
  congr 1
  ring

/-- The Fourier phase and source translation factor combine without any
change of integration variable or convergence convention. -/
theorem fourier_pointFrequencyDensity (s : ℂ) (y : ℝ) (w : UpperHalfPlane) (x : ℝ) :
    𝓕 (pointFrequencyDensity s y w) x =
      spatialLaplaceConstantComplex s * ((y * w.im : ℝ) : ℂ) ^ s *
        ∫ J : ℝ,
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((x - w.re : ℝ) : ℂ) * (J : ℂ)) *
            ∫ E : ℝ in Ioi |J|, pointFourierLaplaceDensity s (y + w.im) J E := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun J => by
    simp only [smul_eq_mul, pointFrequencyDensity]
    have hp : Complex.exp (((-2 * Real.pi * J * x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (w.re : ℂ) * (J : ℂ)) =
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((x - w.re : ℝ) : ℂ) * (J : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = (spatialLaplaceConstantComplex s * ((y * w.im : ℝ) : ℂ) ^ s) *
          (Complex.exp (((-2 * Real.pi * J * x : ℝ) : ℂ) * Complex.I) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (w.re : ℂ) * (J : ℂ))) *
          (∫ E : ℝ in Ioi |J|, pointFourierLaplaceDensity s (y + w.im) J E) := by ring
      _ = _ := by rw [hp]; ring

/-- An ordinary cone representation, once proved, determines every real
Fourier coefficient by continuous Fourier inversion, including frequency zero. -/
theorem pointKernel_fourierLaplace_of_representation
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane)
    (hkernel : ∀ x : ℝ, pointKernel s (rowPoint y hy x) w =
      spatialLaplaceConstantComplex s * ((y * w.im : ℝ) : ℂ) ^ s *
        ∫ J : ℝ,
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((x - w.re : ℝ) : ℂ) * (J : ℂ)) *
            ∫ E : ℝ in Ioi |J|, pointFourierLaplaceDensity s (y + w.im) J E)
    (J : ℝ) :
    (∫ x : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (x : ℂ)) *
        pointKernel s (rowPoint y hy x) w) =
      spatialLaplaceConstantComplex s * ((y * w.im : ℝ) : ℂ) ^ s *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (w.re : ℂ)) *
          ∫ E : ℝ in Ioi |J|, pointFourierLaplaceDensity s (y + w.im) J E := by
  rw [← pointFrequencyDensity_neg]
  exact integral_fourier_double_of_eq (fun x => pointKernel s (rowPoint y hy x) w)
    (pointFrequencyDensity s y w) (integrable_pointFrequencyDensity s hs y hy w)
    (integrable_pointHorizontalKernel s hs y hy w)
    (fun x => (hkernel x).trans (fourier_pointFrequencyDensity s y w x).symm)
    (continuous_pointFrequencyDensity s hs y hy w) J

end GapFamily.Analytic.SpatialPoint
