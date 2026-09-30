import GapFamily.Analytic.Foundation.ThresholdAnchorBand
import GapFamily.Analytic.Foundation.SignedMomentIntegral

/-!
# Quantitative bound for the ordinary threshold anchor

A uniform bound on the actual scalar response bounds the normalized density,
its total variation, and its half-energy moment. The signed measure's variation
is supported on the same compact physical band as its reference measure.
-/

noncomputable section

open MeasureTheory Set

namespace GapFamily.Analytic

/-- The normalized density inherits the bandwise response bound. -/
theorem abs_scalarAnchorBandDensity_le (B : ℝ) (ζ : ℝ → ℝ) (M : ℝ)
    (hI : 0 < scalarAnchorSquareMass B ζ)
    (hM : ∀ E ∈ scalarAnchorBand B, |ζ E| ≤ M)
    {E : ℝ} (hE : E ∈ scalarAnchorBand B) :
    |scalarAnchorBandDensity B ζ E| ≤ M / scalarAnchorSquareMass B ζ := by
  rw [scalarAnchorBandDensity, abs_div, abs_of_pos hI]
  exact div_le_div_of_nonneg_right (hM E hE) hI.le

/-- Zero extension preserves the uniform bound on the ordinary numerator. -/
theorem abs_scalarAnchorNumerator_le (B : ℝ) (ζ : ℝ → ℝ) (M : ℝ)
    (hM0 : 0 ≤ M) (hI : 0 < scalarAnchorSquareMass B ζ)
    (hM : ∀ E ∈ scalarAnchorBand B, |ζ E| ≤ M) (E : ℝ) :
    |scalarAnchorNumerator B ζ E| ≤ M / scalarAnchorSquareMass B ζ := by
  by_cases hE : E ∈ scalarAnchorBand B
  · simpa only [scalarAnchorNumerator, indicator_of_mem hE] using
      abs_scalarAnchorBandDensity_le B ζ M hI hM hE
  · simp only [scalarAnchorNumerator, indicator_of_notMem hE, abs_zero]
    exact div_nonneg hM0 hI.le

/-- Exact total variation, expressed as an ordinary integral of the density. -/
theorem scalarAnchorBandMeasure_totalVariation (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    (scalarAnchorBandMeasure B hB ζ hζ).variation.real univ =
      ∫ E, |scalarAnchorBandDensity B ζ E| ∂scalarAnchorReference B :=
  signedDensity_totalVariation (scalarAnchorBandDensity_integrable B hB ζ hζ)

/-- The ordinary total variation obeys the response bound times band mass. -/
theorem scalarAnchorBandMeasure_totalVariation_le (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) (M : ℝ)
    (hM0 : 0 ≤ M) (hI : 0 < scalarAnchorSquareMass B ζ)
    (hM : ∀ E ∈ scalarAnchorBand B, |ζ E| ≤ M) :
    (scalarAnchorBandMeasure B hB ζ hζ).variation.real univ ≤
      M / (2 * scalarAnchorSquareMass B ζ) := by
  let _ := isFiniteMeasure_scalarAnchorReference B hB
  rw [scalarAnchorBandMeasure_totalVariation B hB ζ hζ]
  calc
    _ ≤ ∫ _E, M / scalarAnchorSquareMass B ζ ∂scalarAnchorReference B := by
      apply integral_mono_ae
        (scalarAnchorBandDensity_integrable B hB ζ hζ).abs (integrable_const _)
      filter_upwards [scalarAnchorReference_ae_mem B] with E hE
      exact abs_scalarAnchorBandDensity_le B ζ M hI hM hE
    _ = (scalarAnchorReference B).real univ * (M / scalarAnchorSquareMass B ζ) := by
      rw [integral_const, smul_eq_mul]
    _ ≤ (1 / 2) * (M / scalarAnchorSquareMass B ζ) :=
      mul_le_mul_of_nonneg_right (scalarAnchorReference_mass_le B hB) (div_nonneg hM0 hI.le)
    _ = M / (2 * scalarAnchorSquareMass B ζ) := by ring

/-- The total variation is absolutely continuous with respect to the band reference. -/
theorem scalarAnchorBandMeasure_variation_absolutelyContinuous (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    (scalarAnchorBandMeasure B hB ζ hζ).variation ≪ scalarAnchorReference B := by
  rw [scalarAnchorBandMeasure,
    Measure.variation_withDensityᵥ (scalarAnchorBandDensity_integrable B hB ζ hζ)]
  exact withDensity_absolutelyContinuous _ _

/-- The support statement holds for almost every point of the actual total variation. -/
theorem scalarAnchorBandMeasure_ae_mem (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    ∀ᵐ E ∂(scalarAnchorBandMeasure B hB ζ hζ).variation, E ∈ scalarAnchorBand B :=
  (scalarAnchorBandMeasure_variation_absolutelyContinuous B hB ζ hζ).ae_le
    (scalarAnchorReference_ae_mem B)

/-- In particular the scalar seed is physically supported at energies at most `3B`. -/
theorem scalarAnchorBandMeasure_ae_physical (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    ∀ᵐ E ∂(scalarAnchorBandMeasure B hB ζ hζ).variation, |(0 : ℝ)| ≤ E ∧ E ≤ 3 * B := by
  filter_upwards [scalarAnchorBandMeasure_ae_mem B hB ζ hζ] with E hE
  refine ⟨?_, hE.2⟩
  simp only [abs_zero]
  linarith [hE.1]

/-- The half-energy weight is genuinely integrable against the actual variation. -/
theorem scalarAnchorBandMeasure_sqrt_integrable (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    Integrable Real.sqrt (scalarAnchorBandMeasure B hB ζ hζ).variation := by
  let _ := signedMeasure_isFiniteMeasure_variation (scalarAnchorBandMeasure B hB ζ hζ)
  apply (integrable_const (Real.sqrt (3 * B))).mono'
    Real.continuous_sqrt.aestronglyMeasurable
  filter_upwards [scalarAnchorBandMeasure_ae_mem B hB ζ hζ] with E hE
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hE.2

/-- The half-energy moment has the same quantitative response bound. -/
theorem scalarAnchorBandMeasure_sqrt_integral_le (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) (M : ℝ)
    (hM0 : 0 ≤ M) (hI : 0 < scalarAnchorSquareMass B ζ)
    (hM : ∀ E ∈ scalarAnchorBand B, |ζ E| ≤ M) :
    (∫ E, Real.sqrt E ∂(scalarAnchorBandMeasure B hB ζ hζ).variation) ≤
      Real.sqrt (3 * B) * M / (2 * scalarAnchorSquareMass B ζ) := by
  let _ := signedMeasure_isFiniteMeasure_variation (scalarAnchorBandMeasure B hB ζ hζ)
  calc
    _ ≤ ∫ _E, Real.sqrt (3 * B) ∂(scalarAnchorBandMeasure B hB ζ hζ).variation := by
      apply integral_mono_ae (scalarAnchorBandMeasure_sqrt_integrable B hB ζ hζ)
        (integrable_const _)
      filter_upwards [scalarAnchorBandMeasure_ae_mem B hB ζ hζ] with E hE
      exact Real.sqrt_le_sqrt hE.2
    _ = Real.sqrt (3 * B) * (scalarAnchorBandMeasure B hB ζ hζ).variation.real univ := by
      rw [integral_const, smul_eq_mul, mul_comm]
    _ ≤ Real.sqrt (3 * B) * (M / (2 * scalarAnchorSquareMass B ζ)) :=
      mul_le_mul_of_nonneg_left (scalarAnchorBandMeasure_totalVariation_le B hB ζ hζ M hM0 hI hM)
        (Real.sqrt_nonneg _)
    _ = Real.sqrt (3 * B) * M / (2 * scalarAnchorSquareMass B ζ) := by ring

end GapFamily.Analytic
