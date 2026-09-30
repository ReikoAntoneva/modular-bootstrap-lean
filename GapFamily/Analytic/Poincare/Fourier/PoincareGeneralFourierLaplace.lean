import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierThreshold
import GapFamily.Analytic.Poincare.Fourier.PoincareScalarThresholdNormalization
import GapFamily.Analytic.Transform.CosRootReferenceLaplace

/-! The actual threshold Fourier coefficient and its ordinary denominatorwise Laplace output.
The input-spin and input-energy corrections are combined before taking the transform.
-/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory CosRootLaplace PoincareFourierRemainder
open PoincareFourierContinuation PoincareCentralZeta PoincareCentralFactor

/-- The two convergent threshold corrections give a single absolutely summable
family of intact higher Fourier integrals. -/
theorem summable_norm_higherFourierIntegral (y : ℝ) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    Summable (fun n : ℕ => ‖kloostermanSum j J n *
      ∫ t : ℝ, higherFourierKernel (n + 1 : ℕ) y E j J t‖) := by
  have hE := summable_norm_kloosterman_energyFourier_threshold y hy (E : ℂ) j J
  have hJ := summable_norm_fourierRemainder hy j J (s := (1 / 2 : ℂ)) (by norm_num)
  apply (hE.add hJ).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [show higherFourierKernel (n + 1 : ℕ) y E j J =
    (fun t => energyFourierKernel (n + 1 : ℕ) y (E : ℂ) j J (1 / 2 : ℂ) t +
      fourierRemainderKernel (n + 1 : ℕ) y j J (1 / 2 : ℂ) t) from rfl,
    integral_add (integrable_energyFourierKernel (by positivity) hy (E : ℂ) j J (by norm_num))
      (integrable_fourierRemainderKernel (by positivity) hy j J (by norm_num)), mul_add]
  exact norm_add_le _ _

/-- The intact higher integrals sum to the already constructed ordinary Fourier corrections. -/
theorem hasSum_higherFourierIntegral (y : ℝ) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    HasSum (fun n : ℕ => kloostermanSum j J n *
      ∫ t : ℝ, higherFourierKernel (n + 1 : ℕ) y E j J t)
      ((∑' n : ℕ, kloostermanSum j J n *
        ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y (E : ℂ) j J (1 / 2 : ℂ) t) +
          fourierRemainder y j J (1 / 2 : ℂ)) := by
  have hE := (summable_norm_kloosterman_energyFourier_threshold y hy (E : ℂ) j J).of_norm.hasSum
  have hJ := hasSum_fourierRemainder hy j J (s := (1 / 2 : ℂ)) (by norm_num)
  convert hE.add hJ using 1
  funext n
  rw [show higherFourierKernel (n + 1 : ℕ) y E j J =
    (fun t => energyFourierKernel (n + 1 : ℕ) y (E : ℂ) j J (1 / 2 : ℂ) t +
      fourierRemainderKernel (n + 1 : ℕ) y j J (1 / 2 : ℂ) t) from rfl,
    integral_add (integrable_energyFourierKernel (by positivity) hy (E : ℂ) j J (by norm_num))
      (integrable_fourierRemainderKernel (by positivity) hy j J (by norm_num)), mul_add]

/-- The actual threshold Fourier coefficient has one intact higher denominator sum. -/
theorem generalThresholdFourierCoefficient_eq_central_add_higher
    (y : ℝ) (hy : 0 < y) (E : ℝ) (j J : ℤ) (hj : j ≠ 0) :
    generalThresholdFourierCoefficient y hy (E : ℂ) j J =
      (if j = J then (y : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) else 0) +
      centralFourierFactor y j 0 * centralZeta j J 0 +
        ∑' n : ℕ, kloostermanSum j J n *
          ∫ t : ℝ, higherFourierKernel (n + 1 : ℕ) y E j J t := by
  rw [(hasSum_higherFourierIntegral y hy E j J).tsum_eq,
    generalThresholdFourierCoefficient_eq_central_add_energy y hy (E : ℂ) j J hj]
  ring

/-- The denominatorwise ordinary Laplace transforms are absolutely summable.
This statement does not exchange the denominator sum with the energy integral. -/
theorem summable_norm_higherKernelTerm_laplace (y : ℝ) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    Summable (fun n : ℕ => ‖(Real.sqrt y : ℂ) * ∫ e,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        (2 * higherKernelTerm j J (e : ℂ) (E : ℂ) n) ∂referenceMeasure j‖) := by
  simpa only [← integral_higherFourierKernel_eq_higherKernelTerm hy E j J] using
    summable_norm_higherFourierIntegral y hy E j J

/-- The exact actual threshold coefficient is the sum of ordinary Laplace transforms
of the source cosRoot brackets, after its direct and central contributions are removed. -/
theorem hasSum_higherKernelTerm_laplace_threshold (y : ℝ) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) (hj : j ≠ 0) :
    HasSum (fun n : ℕ => (Real.sqrt y : ℂ) * ∫ e,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        (2 * higherKernelTerm j J (e : ℂ) (E : ℂ) n) ∂referenceMeasure j)
      (generalThresholdFourierCoefficient y hy (E : ℂ) j J -
        (if j = J then (y : ℂ) ^ (1 / 2 : ℂ) *
          Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) else 0) -
            centralFourierFactor y j 0 * centralZeta j J 0) := by
  rw [generalThresholdFourierCoefficient_eq_central_add_higher y hy E j J hj]
  have h := (summable_norm_higherFourierIntegral y hy E j J).of_norm.hasSum
  convert h using 1
  · funext n
    exact (integral_higherFourierKernel_eq_higherKernelTerm hy E j J n).symm
  · ring

/-- The scalar row has the same intact higher denominator sum and its separately
normalized threshold atom. This includes zero input spin and negative input energy. -/
theorem generalThresholdFourierCoefficient_scalar_eq_threshold_add_higher
    (y : ℝ) (hy : 0 < y) (E : ℝ) (J : ℤ) :
    generalThresholdFourierCoefficient y hy (E : ℂ) 0 J =
      (if J = 0 then (Real.sqrt y : ℂ) *
        Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) else 0) +
      (Real.sqrt y : ℂ) * PoincareScalarFourier.scalarThresholdCoefficient J +
        ∑' n : ℕ, kloostermanSum 0 J n *
          ∫ t : ℝ, higherFourierKernel (n + 1 : ℕ) y E 0 J t := by
  rw [(hasSum_higherFourierIntegral y hy E 0 J).tsum_eq,
    PoincareScalarFourier.generalThresholdFourierCoefficient_zero_eq_direct_add_threshold_add_corrections]
  ring

/-- The scalar continuum is the sum of the ordinary cosRoot-bracket Laplace
transforms; the threshold atom remains separate from its open-half-line measure. -/
theorem hasSum_higherKernelTerm_laplace_threshold_scalar (y : ℝ) (hy : 0 < y)
    (E : ℝ) (J : ℤ) :
    HasSum (fun n : ℕ => (Real.sqrt y : ℂ) * ∫ e,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        (2 * higherKernelTerm 0 J (e : ℂ) (E : ℂ) n) ∂referenceMeasure 0)
      (generalThresholdFourierCoefficient y hy (E : ℂ) 0 J -
        (if J = 0 then (Real.sqrt y : ℂ) *
          Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) else 0) -
            (Real.sqrt y : ℂ) * PoincareScalarFourier.scalarThresholdCoefficient J) := by
  rw [generalThresholdFourierCoefficient_scalar_eq_threshold_add_higher y hy E J]
  have h := (summable_norm_higherFourierIntegral y hy E 0 J).of_norm.hasSum
  convert h using 1
  · funext n
    exact (integral_higherFourierKernel_eq_higherKernelTerm hy E 0 J n).symm
  · ring

end GapFamily.Analytic.PoincareEnergyFourier
