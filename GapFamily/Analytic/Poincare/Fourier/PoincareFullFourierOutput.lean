import GapFamily.Analytic.Poincare.Fourier.PoincareFullFourierLaplace
import GapFamily.Analytic.Poincare.Fourier.PoincareGeneralFourierCircle
import GapFamily.Analytic.Kernel.FullKernelThermal

/-! Absolute spin summation and complete Fourier–Laplace reconstruction of the
actual canonical threshold seed. The direct input and threshold atom remain
separate from the induced ordinary reference density.
-/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory CosRootLaplace PoincareEnergyContinuation
open PoincareFourier PoincareFourierContinuation

private theorem thermal_exponent_eq (y e : ℝ) :
    -((2 * Real.pi * y : ℝ) : ℂ) * (e : ℂ) =
      -2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ) := by
  push_cast
  ring

/-- Absolute thermal mass of the full induced output is summable in every
integer output spin, for arbitrary complex input energy. -/
theorem summable_integral_norm_fullKernelHol_laplace (y : ℝ) (hy : 0 < y)
    (E : ℂ) (J : ℤ) :
    Summable (fun j : ℤ => ∫ e : ℝ,
      ‖Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j J (e : ℂ) E‖ ∂referenceMeasure j) := by
  simpa only [thermal_exponent_eq] using
    summable_integral_norm_thermal_fullKernelHol_spin J E
      (show 0 < 2 * Real.pi * y by positivity)

/-- The full induced Fourier coefficients are absolutely summable. -/
theorem summable_norm_fullKernelHol_laplace (y : ℝ) (hy : 0 < y)
    (E : ℂ) (J : ℤ) :
    Summable (fun j : ℤ => ‖(Real.sqrt y : ℂ) * ∫ e : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j J (e : ℂ) E ∂referenceMeasure j‖) := by
  have hi : Summable (fun j : ℤ => ‖∫ e : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j J (e : ℂ) E ∂referenceMeasure j‖) :=
    (summable_integral_norm_fullKernelHol_laplace y hy E J).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
  simpa only [norm_mul] using hi.mul_left ‖(Real.sqrt y : ℂ)‖

/-- The actual threshold Fourier coefficients are summable, by their full
ordinary density output and the two finitely supported atomic contributions. -/
theorem summable_generalThresholdFourierCoefficient (y : ℝ) (hy : 0 < y)
    (E : ℝ) (J : ℤ) :
    Summable (fun j : ℤ => generalThresholdFourierCoefficient y hy (E : ℂ) j J) := by
  have hd := (hasSum_ite_eq J ((Real.sqrt y : ℂ) *
    Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)))).summable
  have ha := (hasSum_ite_eq (0 : ℤ)
    ((Real.sqrt y : ℂ) * PoincareScalarFourier.scalarThresholdCoefficient J)).summable
  have hi := (summable_norm_fullKernelHol_laplace y hy (E : ℂ) J).of_norm
  exact ((hd.add ha).add hi).congr
    (fun j => (generalThresholdFourierCoefficient_eq_full_laplace y hy E j J).symm)

/-- The actual coefficients reconstruct the continuous horizontal circle in
uniform norm, without a supplied summability hypothesis. -/
theorem hasSum_generalThresholdCircle (y : ℝ) (hy : 0 < y)
    (E : ℝ) (J : ℤ) :
    HasSum (fun j : ℤ => generalThresholdFourierCoefficient y hy (E : ℂ) j J •
      (fourier j : C(AddCircle (1 : ℝ), ℂ))) (generalThresholdCircle y hy (E : ℂ) J) :=
  hasSum_generalThresholdCircle_of_summable y hy (E : ℂ) J
    (summable_generalThresholdFourierCoefficient y hy E J)

/-- The actual global threshold seed equals its ordinary Fourier series at
every horizontal point and every positive height. -/
theorem hasSum_generalThresholdSeed_row (y : ℝ) (hy : 0 < y)
    (E : ℝ) (J : ℤ) (x : ℝ) :
    HasSum (fun j : ℤ => generalThresholdFourierCoefficient y hy (E : ℂ) j J *
      cuspFourierMode j x) (generalThresholdSeed (E : ℂ) J (rowPoint y hy x)) :=
  hasSum_generalThresholdSeed_row_of_summable y hy (E : ℂ) J
    (summable_generalThresholdFourierCoefficient y hy E J) x

/-- The whole induced spin output has absolutely summable ordinary thermal
transforms, including its scalar row and every negative real input energy. -/
theorem summable_norm_fullKernelHol_fourier_laplace (y : ℝ) (hy : 0 < y)
    (E : ℂ) (J : ℤ) (x : ℝ) :
    Summable (fun j : ℤ => ‖((Real.sqrt y : ℂ) * ∫ e : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j J (e : ℂ) E ∂referenceMeasure j) * cuspFourierMode j x‖) := by
  simpa only [norm_mul, norm_cuspFourierMode, mul_one] using
    summable_norm_fullKernelHol_laplace y hy E J

/-- Summing the actual induced Fourier–Laplace output reconstructs the actual
seed after its direct point input and scalar threshold atom are removed. -/
theorem hasSum_fullKernelHol_fourier_laplace (y : ℝ) (hy : 0 < y)
    (E : ℝ) (J : ℤ) (x : ℝ) :
    HasSum (fun j : ℤ => ((Real.sqrt y : ℂ) * ∫ e : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j J (e : ℂ) (E : ℂ) ∂referenceMeasure j) * cuspFourierMode j x)
      (generalThresholdSeed (E : ℂ) J (rowPoint y hy x) -
        (Real.sqrt y : ℂ) *
          Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) * cuspFourierMode J x -
        (Real.sqrt y : ℂ) * PoincareScalarFourier.scalarThresholdCoefficient J) := by
  have hf := hasSum_generalThresholdSeed_row y hy E J x
  have hd := hasSum_ite_eq J ((Real.sqrt y : ℂ) *
    Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) * cuspFourierMode J x)
  have ha := hasSum_ite_eq (0 : ℤ)
    ((Real.sqrt y : ℂ) * PoincareScalarFourier.scalarThresholdCoefficient J)
  convert (hf.sub hd).sub ha using 1
  funext j
  rw [generalThresholdFourierCoefficient_eq_full_laplace]
  by_cases hd : j = J <;> by_cases hz : j = 0
  all_goals subst_vars
  all_goals simp_all only [ite_true, ite_false, cuspFourierMode_zero, mul_one]
  all_goals ring

/-- Complete ordinary Fourier–Laplace decomposition of the actual canonical
threshold seed. The induced continuum uses the strict physical reference
measure; all of its thermal integrals and its spin sum genuinely converge. -/
theorem generalThresholdSeed_eq_full_fourier_laplace (y : ℝ) (hy : 0 < y)
    (E : ℝ) (J : ℤ) (x : ℝ) :
    generalThresholdSeed (E : ℂ) J (rowPoint y hy x) =
      (Real.sqrt y : ℂ) *
        Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) * cuspFourierMode J x +
      (Real.sqrt y : ℂ) * PoincareScalarFourier.scalarThresholdCoefficient J +
      ∑' j : ℤ, ((Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          fullKernelHol j J (e : ℂ) (E : ℂ) ∂referenceMeasure j) * cuspFourierMode j x := by
  rw [(hasSum_fullKernelHol_fourier_laplace y hy E J x).tsum_eq]
  ring

end GapFamily.Analytic.PoincareEnergyFourier
