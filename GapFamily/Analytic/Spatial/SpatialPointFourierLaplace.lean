import GapFamily.Analytic.Spatial.SpatialPointGammaCone
import GapFamily.Analytic.Spatial.SpatialPointFourierDensity

/-! The ordinary point Fourier--Laplace transform, proved from the complex
Gamma integral, an ordinary cone change of variables, and Fourier inversion.
Every convergence premise is proved; no computation axiom is used. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set MeasureTheory PoincareFourier

private theorem pointGammaConeDensity_phase (s z w : ℂ) (J E : ℝ) :
    pointGammaConeDensity s z w (E, J) =
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((z.re - w.re : ℝ) : ℂ) * (J : ℂ)) *
        pointFourierLaplaceDensity s (z.im + w.im) J E := by
  unfold pointGammaConeDensity pointFourierLaplaceDensity
  have hp : Complex.exp (-2 * Real.pi *
      (((z.im + w.im) * E : ℝ) + Complex.I * ((z.re - w.re) * J : ℝ))) =
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((z.re - w.re : ℝ) : ℂ) * (J : ℂ)) *
        Complex.exp ((-2 * Real.pi * (z.im + w.im) * E : ℝ) : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hp]
  ring

/-- The actual kernel is the ordinary iterated frequency integral, with the
exact source translation phase. The inner integral converges almost everywhere. -/
theorem pointKernel_eq_frequency_laplace (s : ℂ) (hs : 0 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) (x : ℝ) :
    pointKernel s (rowPoint y hy x) w =
      spatialLaplaceConstantComplex s * ((y * w.im : ℝ) : ℂ) ^ s *
        ∫ J : ℝ,
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((x - w.re : ℝ) : ℂ) * (J : ℂ)) *
            ∫ E : ℝ in Ioi |J|, pointFourierLaplaceDensity s (y + w.im) J E := by
  rw [pointKernel_eq_frequency_gammaLaplace hs hy w.im_pos]
  congr 1
  apply integral_congr_ae
  filter_upwards with J
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro E _
  exact pointGammaConeDensity_phase s (rowPoint y hy x) w J E

/-- The scalar point Fourier--Laplace identity with all ordinary convergence
and continuity conditions discharged in Lean, for every real frequency. -/
theorem pointKernel_real_fourier_eq_laplace (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) (J : ℝ) :
    (∫ x : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (x : ℂ)) *
        pointKernel s (rowPoint y hy x) w) =
      spatialLaplaceConstantComplex s * ((y * w.im : ℝ) : ℂ) ^ s *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (w.re : ℂ)) *
        ∫ E : ℝ in Ioi |J|, pointFourierLaplaceDensity s (y + w.im) J E :=
  pointKernel_fourierLaplace_of_representation s hs y hy w
    (pointKernel_eq_frequency_laplace s (by linarith) y hy w) J

/-- Integer Fourier projection in the convention used by the actual
horizontal periodization theorem. -/
theorem pointKernel_fourier_eq_laplace (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) (J : ℤ) :
    (∫ x : ℝ, cuspFourierMode (-J) x * pointKernel s (rowPoint y hy x) w) =
      spatialLaplaceConstantComplex s * ((y * w.im : ℝ) : ℂ) ^ s *
        cuspFourierMode (-J) w.re *
        ∫ E : ℝ in Ioi |(J : ℝ)|, pointFourierLaplaceDensity s (y + w.im) J E := by
  have hphase (x : ℝ) : cuspFourierMode (-J) x =
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((J : ℝ) : ℂ) * (x : ℂ)) := by
    unfold cuspFourierMode
    congr 1
    push_cast
    ring
  simp_rw [hphase]
  exact pointKernel_real_fourier_eq_laplace s hs y hy w J

/-- The normally convergent translation sum has the same-parameter ordinary
cone Laplace coefficient, with its exact scalar normalization. -/
theorem pointHorizontalKernel_periodization_eq_laplace (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) (J : ℤ) :
    (∫ x : ℝ in 0..1, cuspFourierMode (-J) x *
      ∑' n : ℤ, pointKernel s (rowPoint y hy (x + n)) w) =
      spatialLaplaceConstantComplex s * ((y * w.im : ℝ) : ℂ) ^ s *
        cuspFourierMode (-J) w.re *
        ∫ E : ℝ in Ioi |(J : ℝ)|, pointFourierLaplaceDensity s (y + w.im) J E := by
  rw [pointHorizontalKernel_periodization_fourier_integral s hs y hy w J]
  exact pointKernel_fourier_eq_laplace s hs y hy w J

end GapFamily.Analytic.SpatialPoint
