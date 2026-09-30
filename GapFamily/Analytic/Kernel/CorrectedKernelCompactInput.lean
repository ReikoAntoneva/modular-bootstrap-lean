import GapFamily.Analytic.Kernel.FullKernelCompactInput
import GapFamily.Analytic.Kernel.FullKernelSmoothingSeed
import GapFamily.Analytic.Poincare.Fourier.PoincareCorrectedFourierLaplace
import GapFamily.Analytic.Foundation.SignedFubini

/-! The actual rank-corrected signed output has ordinary, spin-summable thermal mass. -/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory

/-- Only the scalar output channel carries the rank correction. -/
theorem correctedKernel_eq_fullKernelHol_of_output_ne_zero {j : ℤ} (hj : j ≠ 0)
    (J : ℤ) (e E : ℝ) :
    correctedKernel j J e E = fullKernelHol j J e E := by
  simp only [correctedKernel, scalarRankKernel, hj, false_and, ite_false,
    Complex.ofReal_zero, add_zero]

/-- The complete corrected kernel is absolutely integrable on the actual input-output product. -/
theorem integrable_thermal_correctedKernel_compactInput_prod (ν : SignedMeasure ℝ)
    (j J : ℤ) (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : ℝ × ℝ => Complex.exp (-(t : ℂ) * (p.2 : ℂ)) *
      correctedKernel j J p.2 p.1) (ν.variation.prod (referenceMeasure j)) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have hr := PoincareEnergyFourier.integrable_scalarRankKernel_thermal_prod
    ν.variation B (hs.mono fun _ hE => hE.2) t ht j J
  convert (integrable_thermal_fullKernelHol_compactInput_prod ν j J B hs ht).add hr using 1
  ext p
  exact mul_add _ _ _

/-- The ordinary product absolute masses are summable over all integer output spins. -/
theorem summable_integral_norm_thermal_correctedKernel_compactInput_prod (ν : SignedMeasure ℝ)
    (J : ℤ) (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ p : ℝ × ℝ,
      ‖Complex.exp (-(t : ℂ) * (p.2 : ℂ)) * correctedKernel j J p.2 p.1‖
        ∂ν.variation.prod (referenceMeasure j)) := by
  apply (summable_integral_norm_thermal_fullKernelHol_compactInput_prod ν J B hs ht).congr_cofinite
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with j hj
  simp only [correctedKernel_eq_fullKernelHol_of_output_ne_zero hj]

/-- The corrected and uncorrected signed responses agree in every nonzero output spin. -/
theorem correctedSignedRowResponse_eq_full_of_output_ne_zero (ν : SignedMeasure ℝ)
    (J : ℤ) {j : ℤ} (hj : j ≠ 0) (e : ℝ) :
    correctedSignedRowResponse ν J j e = fullKernelSignedRowResponse ν J j e := by
  simp only [correctedSignedRowResponse, fullKernelSignedRowResponse,
    correctedKernel_eq_fullKernelHol_of_output_ne_zero hj]

/-- The actual corrected signed response has an ordinary thermal integral, including scalar spin. -/
theorem integrable_thermal_correctedSignedRowResponse (ν : SignedMeasure ℝ) (J j : ℤ)
    (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun e : ℝ => Complex.exp (-(t : ℂ) * (e : ℂ)) *
      correctedSignedRowResponse ν J j e) (referenceMeasure j) := by
  have hi := integrable_signedIntegral_of_integrable_prod
    (f := fun E e : ℝ => Complex.exp (-(t : ℂ) * (e : ℂ)) * correctedKernel j J e E)
    (integrable_thermal_correctedKernel_compactInput_prod ν j J B hs ht)
  have heq : (fun e : ℝ => ∫ᵛ E, Complex.exp (-(t : ℂ) * (e : ℂ)) *
      correctedKernel j J e E ∂<•ν) =
      (fun e : ℝ => Complex.exp (-(t : ℂ) * (e : ℂ)) * correctedSignedRowResponse ν J j e) := by
    funext e
    exact signedIntegral_const_mul (correctedSignedRowResponse_integrable ν J j B hs e) _
  rwa [heq] at hi

/-- The actual corrected signed row has absolutely summable thermal mass across all spins. -/
theorem summable_integral_norm_thermal_correctedSignedRowResponse (ν : SignedMeasure ℝ)
    (J : ℤ) (B : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ e : ℝ,
      ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * correctedSignedRowResponse ν J j e‖
        ∂referenceMeasure j) := by
  apply (summable_integral_norm_thermal_fullKernelSignedRowResponse ν J B hs ht).congr_cofinite
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with j hj
  simp only [correctedSignedRowResponse_eq_full_of_output_ne_zero ν J hj]

end GapFamily.Analytic
