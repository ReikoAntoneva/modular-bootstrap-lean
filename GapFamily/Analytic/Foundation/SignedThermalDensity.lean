import GapFamily.Analytic.Foundation.SignedDensityIntegral

/-! Thermal weighting of an ordinary signed density multiplies that density
by the actual exponential. The support hypothesis concerns the underlying
positive measure and therefore also applies to a restricted energy band.
-/

namespace GapFamily.Analytic

open MeasureTheory Set

/-- Weighting an integrable signed density agrees with multiplying its ordinary
density, provided the weight is integrable for the actual variation measure. -/
theorem signedDensity_withDensity_mul
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {q f : α → ℝ}
    (hq : Integrable q μ) (hf : (μ.withDensityᵥ q).Integrable f) :
    (μ.withDensityᵥ q).withDensity f
        (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip =
      μ.withDensityᵥ (fun E => f E * q E) := by
  classical
  have hprod : Integrable (fun E => f E * q E) μ := by
    simpa only [smul_eq_mul, mul_comm] using signedDensity_integrable_smul hq hf
  ext s hs
  rw [VectorMeasure.withDensity_apply hf, withDensityᵥ_apply hprod hs,
    ← VectorMeasure.integral_indicator hs,
    signedDensity_integral_eq_integral_smul hq (hf.indicator hs),
    ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards with E
  by_cases hE : E ∈ s <;> simp [hE, smul_eq_mul, mul_comm]

/-- A nonnegative thermal parameter gives a bounded weight on nonnegative
energy support, hence an actual integrable signed-density pairing. -/
theorem signedDensity_integrable_thermal {μ : Measure ℝ} {q : ℝ → ℝ}
    (hq : Integrable q μ) (hpos : ∀ᵐ E ∂μ, 0 ≤ E) {t : ℝ} (ht : 0 ≤ t) :
    (μ.withDensityᵥ q).Integrable (fun E => Real.exp (-t * E)) := by
  apply (signedDensity_pairing_of_norm_bdd (C := 1) hq (by fun_prop) ?_).1
  filter_upwards [hpos] with E hE
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hE

/-- The thermal multiplication of the ordinary density is itself integrable. -/
theorem signedDensity_integrable_thermal_mul {μ : Measure ℝ} {q : ℝ → ℝ}
    (hq : Integrable q μ) (hpos : ∀ᵐ E ∂μ, 0 ≤ E) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun E => Real.exp (-t * E) * q E) μ := by
  simpa only [smul_eq_mul, mul_comm] using
    signedDensity_integrable_smul hq (signedDensity_integrable_thermal hq hpos ht)

/-- The actual thermal tilt of a signed density on nonnegative energies is
the ordinary measure with its exponentially weighted density. -/
theorem signedDensity_withDensity_thermal {μ : Measure ℝ} {q : ℝ → ℝ}
    (hq : Integrable q μ) (hpos : ∀ᵐ E ∂μ, 0 ≤ E) {t : ℝ} (ht : 0 ≤ t) :
    (μ.withDensityᵥ q).withDensity (fun E => Real.exp (-t * E))
        (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip =
      μ.withDensityᵥ (fun E => Real.exp (-t * E) * q E) :=
  signedDensity_withDensity_mul hq (signedDensity_integrable_thermal hq hpos ht)

end GapFamily.Analytic
