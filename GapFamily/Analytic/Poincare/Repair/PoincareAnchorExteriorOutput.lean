import GapFamily.Analytic.Poincare.Repair.PoincareCanonicalLocalRepair
import GapFamily.Analytic.Poincare.Fourier.PoincareLowBandThermalOutput
import GapFamily.Analytic.Poincare.Fourier.PoincareExteriorThermalOutput

/-! The actual exterior numerator of the canonical anchor. Its direct high-band
scalar density is retained alongside the actual finite corrected kernel response.
Every positive thermal tilt is an ordinary integrable density on the physical
reference measure.
-/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory
open scoped Classical BigOperators

/-- The actual exterior anchor numerator includes the direct high scalar input
and the full corrected response of the actual canonical anchor. -/
def canonicalAnchorExteriorNumerator (B : ℝ) (hB : 1 ≤ B) (j : ℤ) (e : ℝ) : ℝ :=
  (if j = 0 then scalarAnchorNumerator B
    (scalarAnchorResponsePhysical (fun J : lowBandSpinSet B => (J : ℤ)) B
      (zero_le_one.trans hB)) e else 0) +
  (correctedSignedResponse (fun J : lowBandSpinSet B => canonicalLocalAnchorInput B hB J)
    Subtype.val j e).re

/-- The finite response is the literal sum over the canonical physical spin set. -/
theorem canonicalAnchorExteriorNumerator_eq_sum
    (B : ℝ) (hB : 1 ≤ B) (j : ℤ) (e : ℝ) :
    canonicalAnchorExteriorNumerator B hB j e =
      (if j = 0 then scalarAnchorNumerator B
        (scalarAnchorResponsePhysical (fun J : lowBandSpinSet B => (J : ℤ)) B
          (zero_le_one.trans hB)) e else 0) +
      ∑ J ∈ lowBandSpinSet B, (correctedSignedRowResponse
        (canonicalLocalAnchorInput B hB J) J j e).re := by
  rw [canonicalAnchorExteriorNumerator, correctedSignedResponse, Complex.re_sum]
  congr 1
  exact Finset.sum_coe_sort (lowBandSpinSet B) (fun J =>
    (correctedSignedRowResponse (canonicalLocalAnchorInput B hB J) J j e).re)

/-- The real numerator is exactly the actual complex direct-plus-response
formula: kernel reality removes no component by fiat. -/
theorem canonicalAnchorExteriorNumerator_coe
    (B : ℝ) (hB : 1 ≤ B) (j : ℤ) (e : ℝ) :
    (canonicalAnchorExteriorNumerator B hB j e : ℂ) =
      ((if j = 0 then scalarAnchorNumerator B
        (scalarAnchorResponsePhysical (fun J : lowBandSpinSet B => (J : ℤ)) B
          (zero_le_one.trans hB)) e else 0 : ℝ) : ℂ) +
      correctedSignedResponse (fun J : lowBandSpinSet B => canonicalLocalAnchorInput B hB J)
        Subtype.val j e := by
  rw [canonicalAnchorExteriorNumerator, Complex.ofReal_add]
  congr 1
  exact correctedSignedResponse_ofReal_re
    (fun J : lowBandSpinSet B => canonicalLocalAnchorInput B hB J)
    Subtype.val j (3 * B)
    (fun J => canonicalLocalAnchorInput_physicalSupport B hB J) e

/-- The direct scalar part has an ordinary thermal integral. -/
theorem integrable_canonicalAnchorDirectNumerator_thermal
    (B : ℝ) (hB : 1 ≤ B) (j : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun e => Real.exp (-t * e) *
      (if j = 0 then scalarAnchorNumerator B
        (scalarAnchorResponsePhysical (fun J : lowBandSpinSet B => (J : ℤ)) B
          (zero_le_one.trans hB)) e else 0)) (referenceMeasure j) := by
  by_cases hj : j = 0
  · subst j
    simp only [ite_true]
    apply signedDensity_integrable_thermal_mul
      (scalarAnchorNumerator_integrable B (by linarith) _
        (continuous_scalarAnchorResponsePhysical _ B (zero_le_one.trans hB)).continuousOn) _ ht
    filter_upwards [referenceMeasure_ae_above_edge 0] with e he
    simpa only [Int.cast_zero, abs_zero] using he.le
  · simp only [ite_eq_right hj, mul_zero]
    exact integrable_zero _ _ _

/-- The actual complete exterior numerator has an ordinary absolutely
convergent thermal integral, including its direct high-band density. -/
theorem integrable_canonicalAnchorExteriorNumerator_thermal
    (B : ℝ) (hB : 1 ≤ B) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun e => Real.exp (-t * e) * canonicalAnchorExteriorNumerator B hB j e)
      (referenceMeasure j) := by
  have hc := integrable_finiteCorrectedThermalDensity (lowBandSpinSet B)
    (canonicalLocalAnchorInput B hB) j (3 * B)
    (fun J _ => canonicalLocalAnchorInput_physicalSupport B hB J) ht
  convert (integrable_canonicalAnchorDirectNumerator_thermal B hB j ht.le).add hc using 1
  ext e
  exact mul_add _ _ _

/-- The high scalar anchor measure is unchanged when restricted strictly above
`B`, since its actual variation is carried by `[2B,3B]`. -/
theorem scalarAnchorBandMeasure_restrict_Ioi (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    (scalarAnchorBandMeasure B hB ζ hζ).restrict (Ioi B) =
      scalarAnchorBandMeasure B hB ζ hζ := by
  apply signedMeasure_restrict_eq_self_of_ae_mem _ _ measurableSet_Ioi
  filter_upwards [scalarAnchorBandMeasure_ae_mem B hB ζ hζ] with e he
  change B < e
  have hh : 2 * B ≤ e := he.1
  linarith

/-- Above the cutoff the literal scalar input is the ordinary zero-extended
high-band numerator against the actual restricted reference measure. -/
theorem scalarAnchorBandMeasure_eq_exterior_referenceDensity
    (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    scalarAnchorBandMeasure B hB ζ hζ =
      ((referenceMeasure 0).restrict (Ioi B)).withDensityᵥ (scalarAnchorNumerator B ζ) := by
  calc
    _ = (scalarAnchorBandMeasure B hB ζ hζ).restrict (Ioi B) :=
      (scalarAnchorBandMeasure_restrict_Ioi B hB ζ hζ).symm
    _ = _ := by
      ext s hs
      rw [VectorMeasure.restrict_apply _ measurableSet_Ioi hs,
        scalarAnchorBandMeasure_eq_referenceDensity B hB ζ hζ,
        withDensityᵥ_apply (scalarAnchorNumerator_integrable B hB ζ hζ)
          (hs.inter measurableSet_Ioi),
        withDensityᵥ_apply (scalarAnchorNumerator_integrable B hB ζ hζ).restrict hs,
        Measure.restrict_restrict hs]

/-- Thermal tilting retains the exact direct scalar exterior density. -/
theorem thermalSignedInputMeasure_scalarAnchorBandMeasure_exterior
    (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B)) {t : ℝ} (ht : 0 ≤ t) :
    thermalSignedInputMeasure (scalarAnchorBandMeasure B hB ζ hζ) t =
      ((referenceMeasure 0).restrict (Ioi B)).withDensityᵥ
        (fun e => Real.exp (-t * e) * scalarAnchorNumerator B ζ e) := by
  rw [scalarAnchorBandMeasure_eq_exterior_referenceDensity B hB ζ hζ]
  apply signedDensity_withDensity_thermal
    (scalarAnchorNumerator_integrable B hB ζ hζ).restrict _ ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
  exact (hB.trans he).le

/-- Above the cutoff the actual inverse input vanishes, leaving precisely the
ordinary high scalar-band input of the canonical anchor. -/
theorem canonicalLocalAnchorInput_restrict_Ioi
    (B : ℝ) (hB : 1 ≤ B) (j : ℤ) :
    (canonicalLocalAnchorInput B hB j).restrict (Ioi B) =
      if j = 0 then scalarAnchorBandMeasure B (by linarith)
        (scalarAnchorResponsePhysical (fun J : lowBandSpinSet B => (J : ℤ)) B
          (zero_le_one.trans hB))
        (continuous_scalarAnchorResponsePhysical _ B (zero_le_one.trans hB)).continuousOn
      else 0 := by
  unfold canonicalLocalAnchorInput actualLocalAnchorInput localAnchorInput
  simp only [Pi.sub_apply, VectorMeasure.restrict_sub,
    localInverseInput_restrict_Ioi, sub_zero]
  by_cases hj : j = 0 <;>
    simp only [localAnchorHighInput, hj, ite_true, ite_false,
      scalarAnchorBandMeasure_restrict_Ioi, VectorMeasure.restrict_zero]

/-- The exterior direct part of the finite canonical anchor output is exactly
the tilted scalar high-band density, with no inverse density retained there. -/
theorem canonicalLocalAnchor_directExterior_thermal
    (B : ℝ) (hB : 1 ≤ B) (j : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    (if j ∈ lowBandSpinSet B then
      thermalSignedInputMeasure ((canonicalLocalAnchorInput B hB j).restrict (Ioi B)) t
      else 0) =
      ((referenceMeasure j).restrict (Ioi B)).withDensityᵥ
        (fun e => Real.exp (-t * e) *
          (if j = 0 then scalarAnchorNumerator B
            (scalarAnchorResponsePhysical (fun J : lowBandSpinSet B => (J : ℤ)) B
              (zero_le_one.trans hB)) e else 0)) := by
  by_cases hj : j = 0
  · subst j
    have h0 : (0 : ℤ) ∈ lowBandSpinSet B :=
      (zero_mem_lowBandSpinSet B).mpr (by linarith)
    rw [ite_eq_left h0, canonicalLocalAnchorInput_restrict_Ioi, ite_eq_left rfl]
    simp only [ite_true]
    exact thermalSignedInputMeasure_scalarAnchorBandMeasure_exterior B (by linarith) _ _ ht
  · simp [canonicalLocalAnchorInput_restrict_Ioi, hj, thermalSignedInputMeasure]
    exact (withDensityᵥ_zero (μ := (referenceMeasure j).restrict (Ioi B))).symm

/-- Complete ordinary exterior density of the actual canonical anchor. Its
direct high-band scalar numerator is included, and the scalar threshold atom
is excluded by the genuine exterior restriction. -/
theorem canonicalLocalAnchorOutput_restrict_exterior
    (B : ℝ) (hB : 1 ≤ B) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalAnchorInput B hB) j t).restrict (Ioi B) =
      ((referenceMeasure j).restrict (Ioi B)).withDensityᵥ
        (fun e => Real.exp (-t * e) * canonicalAnchorExteriorNumerator B hB j e) := by
  rw [correctedThermalFiniteOutputMeasure_restrict_Ioi (lowBandSpinSet B)
    (canonicalLocalAnchorInput B hB) j (3 * B)
    (fun J _ => canonicalLocalAnchorInput_physicalSupport B hB J) ht B (zero_le_one.trans hB),
    canonicalLocalAnchor_directExterior_thermal B hB j ht.le]
  rw [← withDensityᵥ_add'
    (integrable_canonicalAnchorDirectNumerator_thermal B hB j ht.le).restrict
    (integrable_finiteCorrectedThermalDensity (lowBandSpinSet B)
      (canonicalLocalAnchorInput B hB) j (3 * B)
      (fun J _ => canonicalLocalAnchorInput_physicalSupport B hB J) ht).restrict]
  congr 1
  funext e
  exact (mul_add _ _ _).symm

/-- In the partition-function height convention the exterior density has the
exact weight `exp (-2π t e)` against the actual physical reference measure. -/
theorem canonicalLocalAnchorOutput_restrict_exterior_height
    (B : ℝ) (hB : 1 ≤ B) (j : ℤ) (t : ℝ) (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalAnchorInput B hB) j (2 * Real.pi * t)).restrict (Ioi B) =
      ((referenceMeasure j).restrict (Ioi B)).withDensityᵥ
        (fun e => Real.exp (-2 * Real.pi * t * e) *
          canonicalAnchorExteriorNumerator B hB j e) := by
  simpa only [neg_mul] using
    canonicalLocalAnchorOutput_restrict_exterior B hB j
      (show 0 < 2 * Real.pi * t by positivity)

end GapFamily.Analytic

