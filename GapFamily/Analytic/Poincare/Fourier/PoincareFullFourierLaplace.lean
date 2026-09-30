import GapFamily.Analytic.Poincare.Fourier.PoincareGeneralFourierLaplace
import GapFamily.Analytic.Poincare.Fourier.PoincareCentralLaplace
import GapFamily.Analytic.Kernel.HigherKernelThermal
import GapFamily.Analytic.Kernel.FullKernel

/-! Ordinary Fourier–Laplace output of the actual canonical threshold seed.
Every real input energy is allowed, including the negative vacuum energies.
The direct input, scalar threshold coefficient, and induced reference density
are displayed separately.
-/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory CosRootLaplace PoincareFourierRemainder
open PoincareFourierContinuation PoincareCentralZeta PoincareCentralFactor

private theorem thermal_exponent_eq (y e : ℝ) :
    -((2 * Real.pi * y : ℝ) : ℂ) * (e : ℂ) =
      -2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ) := by
  push_cast
  ring

/-- The higher part has an ordinary absolutely convergent Laplace transform. -/
theorem integrable_higherKernel_laplace (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) :
    Integrable (fun e : ℝ =>
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        higherKernel j J (e : ℂ) E) (referenceMeasure j) := by
  simpa only [thermal_exponent_eq] using
    integrable_thermal_higherKernel j J E (show 0 < 2 * Real.pi * y by positivity)

/-- Ordinary absolute integrability permits summing all cosRoot denominators
inside the physical Laplace integral, while retaining the intact subtraction. -/
theorem tsum_higherFourierIntegral_eq_laplace (y : ℝ) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    (∑' n : ℕ, kloostermanSum j J n *
      ∫ t : ℝ, higherFourierKernel (n + 1 : ℕ) y E j J t) =
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          higherKernel j J (e : ℂ) (E : ℂ) ∂referenceMeasure j := by
  have he := integral_thermal_higherKernel_eq_tsum j J (E : ℂ)
    (show 0 < 2 * Real.pi * y by positivity)
  simp only [thermal_exponent_eq] at he
  rw [he, ← tsum_mul_left]
  apply tsum_congr
  intro n
  exact integral_higherFourierKernel_eq_higherKernelTerm hy E j J n

/-- The scalar output has the actual direct atom and threshold atom, with an
ordinary induced density on the open physical half-line. -/
theorem generalThresholdFourierCoefficient_scalar_eq_laplace
    (y : ℝ) (hy : 0 < y) (E : ℝ) (J : ℤ) :
    generalThresholdFourierCoefficient y hy (E : ℂ) 0 J =
      (if J = 0 then (Real.sqrt y : ℂ) *
        Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) else 0) +
      (Real.sqrt y : ℂ) * PoincareScalarFourier.scalarThresholdCoefficient J +
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          fullKernelHol 0 J (e : ℂ) (E : ℂ) ∂referenceMeasure 0 := by
  rw [generalThresholdFourierCoefficient_scalar_eq_threshold_add_higher,
    tsum_higherFourierIntegral_eq_laplace y hy E 0 J]
  simp only [fullKernelHol, centralKernel_scalar_output, zero_add]

/-- The central density has an ordinary Laplace integral; in the scalar row its
numerator vanishes, so no divergent scalar reference integral is introduced. -/
theorem integrable_centralKernel_laplace (y : ℝ) (hy : 0 < y) (j J : ℤ) :
    Integrable (fun e : ℝ =>
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        centralKernel j J) (referenceMeasure j) := by
  by_cases hj : j = 0
  · subst j
    simp only [centralKernel_scalar_output, mul_zero]
    exact integrable_zero _ _ _
  · simpa only [thermal_exponent_eq] using
      (integrable_centralLaplace_referenceMeasure hy hj).mul_const (centralKernel j J)

/-- The full induced density is ordinarily integrable at every positive
thermal tilt, including arbitrary complex input energy. -/
theorem integrable_fullKernelHol_laplace (y : ℝ) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) :
    Integrable (fun e : ℝ =>
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j J (e : ℂ) E) (referenceMeasure j) := by
  convert! (integrable_centralKernel_laplace y hy j J).add
    (integrable_higherKernel_laplace y hy E j J) using 1
  ext e
  exact mul_add _ _ _

/-- The proved central coefficient is precisely the constant-density part of
`Q_hol`, including its vanishing at zero input spin. -/
theorem centralFourierCoefficient_eq_laplace (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (hj : j ≠ 0) :
    centralFourierFactor y j 0 * centralZeta j J 0 =
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          centralKernel j J ∂referenceMeasure j := by
  by_cases hJ : J = 0
  · subst J
    simp only [centralZeta_zero_input j hj, centralKernel_scalar_input,
      mul_zero, integral_zero]
  · rw [centralKernel, ite_eq_right (not_or.mpr ⟨hj, hJ⟩), integral_mul_const,
      centralFourierFactor_zero_eq_referenceLaplace hy hj]
    ring

/-- Nonzero output spin has the direct input and the complete ordinary induced
density, with no threshold or nonzero-edge atom added. -/
theorem generalThresholdFourierCoefficient_nonzero_eq_laplace
    (y : ℝ) (hy : 0 < y) (E : ℝ) (j J : ℤ) (hj : j ≠ 0) :
    generalThresholdFourierCoefficient y hy (E : ℂ) j J =
      (if j = J then (Real.sqrt y : ℂ) *
        Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) else 0) +
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          fullKernelHol j J (e : ℂ) (E : ℂ) ∂referenceMeasure j := by
  have hp : (y : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt y : ℂ) := by
    calc
      _ = ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        simpa using (Complex.ofReal_cpow hy.le (1 / 2 : ℝ)).symm
      _ = _ := by rw [← Real.sqrt_eq_rpow]
  rw [generalThresholdFourierCoefficient_eq_central_add_higher y hy E j J hj,
    hp, tsum_higherFourierIntegral_eq_laplace y hy E j J, centralFourierCoefficient_eq_laplace y hy j J hj]
  simp only [fullKernelHol, mul_add]
  rw [integral_add (integrable_centralKernel_laplace y hy j J)
    (integrable_higherKernel_laplace y hy (E : ℂ) j J)]
  ring

/-- Complete ordinary Fourier–Laplace output of the actual global threshold seed.
The first term is the original point input, the second is exactly the scalar
threshold coefficient, and the last is the induced density against the physical
reference measure. Every real input energy is permitted. -/
theorem generalThresholdFourierCoefficient_eq_full_laplace
    (y : ℝ) (hy : 0 < y) (E : ℝ) (j J : ℤ) :
    generalThresholdFourierCoefficient y hy (E : ℂ) j J =
      (if j = J then (Real.sqrt y : ℂ) *
        Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) else 0) +
      (if j = 0 then (Real.sqrt y : ℂ) *
        PoincareScalarFourier.scalarThresholdCoefficient J else 0) +
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          fullKernelHol j J (e : ℂ) (E : ℂ) ∂referenceMeasure j := by
  by_cases hj : j = 0
  · subst j
    simpa only [ite_true, eq_comm (a := (0 : ℤ))] using
      generalThresholdFourierCoefficient_scalar_eq_laplace y hy E J
  · simpa only [ite_eq_right hj, add_zero] using
      generalThresholdFourierCoefficient_nonzero_eq_laplace y hy E j J hj

end GapFamily.Analytic.PoincareEnergyFourier
