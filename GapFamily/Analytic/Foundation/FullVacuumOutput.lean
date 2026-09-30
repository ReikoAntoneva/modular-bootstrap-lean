import GapFamily.Analytic.Foundation.FullVacuumDirect
import GapFamily.Analytic.Poincare.Fourier.PoincareFullFourierOutput

/-!
# Complete thermal output of the canonical vacuum

The actual modular four-seed completion equals its prescribed direct vacuum,
its scalar threshold atom, and its absolutely convergent physical continuum.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory UpperHalfPlane CuspFourierCutoff
open PoincareEnergyContinuation PoincareEnergyFourier PoincareScalarFourier
open PoincareFourier

/-- The absolute thermal mass of the complete vacuum continuum is summable
over every integer spin. All four negative-energy seed outputs are included. -/
theorem summable_integral_norm_vacuumFullKernel_laplace
    (a y : ℝ) (hy : 0 < y) :
    Summable (fun j : ℤ => ∫ e : ℝ,
      ‖Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        vacuumFullKernel a e j‖ ∂referenceMeasure j) := by
  have h0 := summable_integral_norm_fullKernelHol_laplace y hy (-a) 0
  have hp := summable_integral_norm_fullKernelHol_laplace y hy (1 - a) 1
  have hm := summable_integral_norm_fullKernelHol_laplace y hy (1 - a) (-1)
  have h2 := summable_integral_norm_fullKernelHol_laplace y hy (2 - a) 0
  apply (((h0.add hp).add hm).add h2).of_nonneg_of_le
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
  intro j
  have i0 := (integrable_fullKernelHol_laplace y hy (-a) j 0).norm
  have ip := (integrable_fullKernelHol_laplace y hy (1 - a) j 1).norm
  have im := (integrable_fullKernelHol_laplace y hy (1 - a) j (-1)).norm
  have i2 := (integrable_fullKernelHol_laplace y hy (2 - a) j 0).norm
  have hb (e : ℝ) :
      ‖Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) * vacuumFullKernel a e j‖ ≤
      ‖Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j 0 (e : ℂ) (-a)‖ +
      ‖Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j 1 (e : ℂ) (1 - a)‖ +
      ‖Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j (-1) (e : ℂ) (1 - a)‖ +
      ‖Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j 0 (e : ℂ) (2 - a)‖ := by
    simp only [vacuumFullKernel, mul_add, mul_sub]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  have hi := integral_mono_ae (integrable_vacuumFullKernel_laplace a y hy j).norm
    (((i0.fun_add ip).fun_add im).fun_add i2) (Filter.Eventually.of_forall hb)
  rw [integral_add ((i0.fun_add ip).fun_add im) i2,
    integral_add (i0.fun_add ip) im, integral_add i0 ip] at hi
  exact hi

/-- The continuum Fourier–Laplace series converges absolutely at every point. -/
theorem summable_norm_vacuumFullKernel_fourier_laplace
    (a y : ℝ) (hy : 0 < y) (x : ℝ) :
    Summable (fun j : ℤ => ‖((Real.sqrt y : ℂ) * ∫ e : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        vacuumFullKernel a e j ∂referenceMeasure j) * cuspFourierMode j x‖) := by
  have hi : Summable (fun j : ℤ => ‖∫ e : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        vacuumFullKernel a e j ∂referenceMeasure j‖) :=
    (summable_integral_norm_vacuumFullKernel_laplace a y hy).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
  simpa only [norm_mul, norm_cuspFourierMode, mul_one] using
    hi.mul_left ‖(Real.sqrt y : ℂ)‖

/-- Summing the continuum of the actual four seeds leaves exactly their
canonical modular completion, direct vacuum, and scalar threshold weight. -/
theorem hasSum_vacuumFullKernel_fourier_laplace
    (a y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => ((Real.sqrt y : ℂ) * ∫ e : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        vacuumFullKernel a e j ∂referenceMeasure j) * cuspFourierMode j x)
      (vacuumReducedSeed a (rowPoint y hy x) - vacuumDirectRow a y x +
        6 * (Real.sqrt y : ℂ)) := by
  have h0 := hasSum_fullKernelHol_fourier_laplace y hy (-a) 0 x
  have hp := hasSum_fullKernelHol_fourier_laplace y hy (1 - a) 1 x
  have hm := hasSum_fullKernelHol_fourier_laplace y hy (1 - a) (-1) x
  have h2 := hasSum_fullKernelHol_fourier_laplace y hy (2 - a) 0 x
  push_cast at h0 hp hm h2
  convert ((h0.sub hp).sub hm).add h2 using 1
  · funext j
    rw [integral_vacuumFullKernel_laplace_eq_four_seed a y hy j]
    ring
  · simp only [vacuumReducedSeed, vacuumDirectRow, cuspFourierMode_zero, mul_one,
      scalarThresholdCoefficient_zero, scalarThresholdCoefficient_one,
      scalarThresholdCoefficient_neg_one]
    ring

/-- Complete Fourier–Laplace output of the actual modular vacuum, with the
same real numerator used in the positivity and remainder estimates. -/
theorem vacuumReducedSeed_eq_full_fourier_laplace
    (a y : ℝ) (hy : 0 < y) (x : ℝ) :
    vacuumReducedSeed a (rowPoint y hy x) =
      vacuumDirectRow a y x - 6 * (Real.sqrt y : ℂ) +
      ∑' j : ℤ, ((Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          (vacuumNumerator a e j : ℂ) ∂referenceMeasure j) * cuspFourierMode j x := by
  simp only [vacuumNumerator_coe_eq]
  rw [(hasSum_vacuumFullKernel_fourier_laplace a y hy x).tsum_eq]
  ring

/-- The completed vacuum has precisely the prescribed character numerator as
its direct part, scalar atom minus six, and the same actual real continuum. -/
theorem vacuumReducedSeed_eq_character_fourier_laplace
    (c : ℝ) (τ : UpperHalfPlane) :
    vacuumReducedSeed (GapFamily.shift c) τ =
      (Real.sqrt τ.im : ℂ) * GapFamily.vacuumNumerator c τ -
        6 * (Real.sqrt τ.im : ℂ) +
      ∑' j : ℤ, ((Real.sqrt τ.im : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (τ.im : ℂ) * (e : ℂ)) *
          (vacuumNumerator (GapFamily.shift c) e j : ℂ) ∂referenceMeasure j) *
        cuspFourierMode j τ.re := by
  have hrow : rowPoint τ.im τ.im_pos τ.re = τ := by
    apply UpperHalfPlane.ext
    exact Complex.eta _
  simpa only [hrow, vacuumDirectRow_eq_vacuumNumerator] using
    vacuumReducedSeed_eq_full_fourier_laplace (GapFamily.shift c) τ.im τ.im_pos τ.re

end GapFamily.Analytic
