import GapFamily.Analytic.Poincare.Fourier.PoincareSignedFourier
import GapFamily.Analytic.Poincare.Fourier.PoincareFullFourierLaplace
import GapFamily.Analytic.Kernel.FullKernelCompactInput
import GapFamily.Analytic.Foundation.SignedFubini

/-! Actual ordinary signed superposition of the complete point-seed
Fourier–Laplace output. Input measures are integrated directly; the induced
continuum is formed by ordinary Fubini with the physical reference measure.
-/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set Filter MeasureTheory PoincareEnergyContinuation PoincareFourier

private theorem thermal_exponent_eq (y e : ℝ) :
    -((2 * Real.pi * y : ℝ) : ℂ) * (e : ℂ) =
      -2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ) := by
  push_cast
  ring

/-- The original finite signed input has an ordinary thermal transform. -/
theorem signedIntegrable_physical_laplace (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) :
    ν.Integrable (fun E : ℝ => Complex.exp (-(t : ℂ) * (E : ℂ))) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  apply (integrable_const (1 : ℝ)).mono'
    (by exact Continuous.aestronglyMeasurable (by fun_prop))
  filter_upwards [hs] with E hE
  rw [norm_exp_thermal]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) ((abs_nonneg _).trans hE.1))

/-- Ordinary Fubini identifies the actual integrated point-seed continuum
with the Laplace transform of the actual signed kernel response. -/
theorem signedIntegral_fullKernelHol_laplace_swap
    (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (y : ℝ) (hy : 0 < y) :
    (∫ᵛ E : ℝ, (∫ e : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelHol j J (e : ℂ) (E : ℂ) ∂referenceMeasure j) ∂<•ν) =
      ∫ e : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        fullKernelSignedRowResponse ν J j e ∂referenceMeasure j := by
  have hp := integrable_thermal_fullKernelHol_compactInput_prod ν j J B hs
    (show 0 < 2 * Real.pi * y by positivity)
  simp only [thermal_exponent_eq] at hp
  rw [signedIntegral_integral_swap (ν := ν) (μ := referenceMeasure j)
    (f := fun E e => Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
      fullKernelHol j J (e : ℂ) (E : ℂ)) hp]
  apply integral_congr_ae
  filter_upwards with e
  exact signedIntegral_const_mul (fullKernelSignedRowResponse_integrable ν J j B hs e) _

/-- The literal ordinary Fourier coefficient of a physical signed row has
exactly its original signed input, central threshold mass, and the actual
ordinary full-kernel response. -/
theorem rowSeedSuperposition_fourier_eq_full_laplace
    (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
      rowSeedSuperposition ν J (rowPoint y hy x)) =
      (if j = J then (Real.sqrt y : ℂ) *
        (∫ᵛ E : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (E : ℂ)) ∂<•ν)
        else 0) +
      (if j = 0 then (Real.sqrt y : ℂ) *
        PoincareScalarFourier.scalarThresholdCoefficient J * (ν univ : ℂ) else 0) +
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          fullKernelSignedRowResponse ν J j e ∂referenceMeasure j := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have he (E : ℝ) : -2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ) =
      -2 * (Real.pi : ℂ) * (y : ℂ) * (E : ℂ) := by ring
  have hi := signedIntegrable_physical_laplace ν J B hs
    (show 0 < 2 * Real.pi * y by positivity)
  simp only [thermal_exponent_eq] at hi
  let A : ℝ → ℂ := fun E => if j = J then
    (Real.sqrt y : ℂ) * Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (E : ℂ)) else 0
  let b : ℂ := if j = 0 then
    (Real.sqrt y : ℂ) * PoincareScalarFourier.scalarThresholdCoefficient J else 0
  let F : ℝ → ℂ := fun E => ∫ e : ℝ,
    Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
      fullKernelHol j J (e : ℂ) (E : ℂ) ∂referenceMeasure j
  have hA : ν.Integrable A := by
    by_cases h : j = J
    · simpa only [A, h, ite_true] using hi.const_mul (Real.sqrt y : ℂ)
    · simp only [A, h, ite_false]
      exact integrable_const (0 : ℂ)
  have hb : ν.Integrable (fun _ : ℝ => b) := integrable_const b
  have hF : ν.Integrable F := by
    have hp := integrable_thermal_fullKernelHol_compactInput_prod ν j J B hs
      (show 0 < 2 * Real.pi * y by positivity)
    simp only [thermal_exponent_eq] at hp
    exact hp.integral_prod_left
  rw [rowSeedSuperposition_fourier y hy ν j J B hs]
  have hformula (E : ℝ) : generalThresholdFourierCoefficient y hy (E : ℂ) j J =
      A E + b + (Real.sqrt y : ℂ) * F E := by
    simpa only [A, b, F, he] using
      generalThresholdFourierCoefficient_eq_full_laplace y hy E j J
  simp_rw [hformula]
  rw [VectorMeasure.integral_fun_add
      (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip)
      (f := fun E => A E + b) (g := fun E => (Real.sqrt y : ℂ) * F E)
      (hA.add hb) (hF.const_mul (Real.sqrt y : ℂ)),
    VectorMeasure.integral_fun_add
      (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip) hA hb,
    signedIntegral_const_mul hF]
  have hAi : (∫ᵛ E, A E ∂<•ν) = if j = J then (Real.sqrt y : ℂ) *
      (∫ᵛ E : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (E : ℂ)) ∂<•ν)
      else 0 := by
    by_cases h : j = J
    · simp only [A, h, ite_true]
      exact signedIntegral_const_mul hi _
    · simp [A, h]
  have hbi : (∫ᵛ _ : ℝ, b ∂<•ν) = if j = 0 then
      (Real.sqrt y : ℂ) * PoincareScalarFourier.scalarThresholdCoefficient J *
        (ν univ : ℂ) else 0 := by
    by_cases h : j = 0 <;> simp [b, h, VectorMeasure.integral_const, Complex.real_smul, mul_comm]
  rw [hAi, hbi]
  congr 1
  congr 1
  exact signedIntegral_fullKernelHol_laplace_swap ν J j B hs y hy

end GapFamily.Analytic.PoincareEnergyFourier
