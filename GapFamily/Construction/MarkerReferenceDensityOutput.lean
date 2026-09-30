import GapFamily.Construction.MarkerReferenceDensity
import GapFamily.Construction.MarkerReferenceOutputSupport

/-!
# The explicit density of the actual reference output

The ordinary thermal measure is precisely the prescribed marker plus the
exponentially weighted explicit density. Consequently its proved support gap
forces this same density to vanish almost everywhere below the cutoff.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace GapFamily.Construction

open Analytic

private theorem reference_ae_nonnegative (j : ℤ) :
    ∀ᵐ e ∂referenceMeasure j, 0 ≤ e :=
  (referenceMeasure_ae_above_edge j).mono fun _ he => (abs_nonneg _).trans he.le

/-- The thermal direct density is ordinarily absolutely integrable. -/
theorem canonicalMarkerReferenceDirectDensity_thermal_integrable (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun e => Real.exp (-t * e) * canonicalMarkerReferenceDirectDensity a b ha hb j e)
      (referenceMeasure j) :=
  signedDensity_integrable_thermal_mul (canonicalMarkerReferenceDirectDensity_integrable a b ha hb j)
    (reference_ae_nonnegative j) ht.le

/-- The full explicit density has ordinary finite thermal mass at every positive temperature. -/
theorem canonicalMarkerReferenceDensity_thermal_integrable (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun e => Real.exp (-t * e) * canonicalMarkerReferenceDensity a b ha hb j e)
      (referenceMeasure j) := by
  have hd := canonicalMarkerReferenceDirectDensity_thermal_integrable a b ha hb j ht
  have hv := integrable_vacuumThermalDensity a j ht
  have hc := integrable_finiteCorrectedThermalDensity (lowBandSpinSet b)
    (canonicalMarkerReferenceInput a b ha hb) j (3 * b)
    (fun J _ => canonicalMarkerReferenceInput_physicalSupport a b ha hb J) ht
  simpa only [Pi.add_apply, canonicalMarkerReferenceDensity, canonicalMarkerReferenceKernelNumerator,
    Analytic.vacuumNumerator, vacuumThermalDensity, mul_add] using! hd.add (hv.add hc)

private theorem thermal_input_add (ν μ : SignedMeasure ℝ) (t : ℝ)
    (hν : ν.Integrable (fun e => Real.exp (-t * e)))
    (hμ : μ.Integrable (fun e => Real.exp (-t * e))) :
    thermalSignedInputMeasure (ν + μ) t =
      thermalSignedInputMeasure ν t + thermalSignedInputMeasure μ t := by
  ext s hs
  rw [thermalSignedInputMeasure, VectorMeasure.withDensity_apply (hν.add_vectorMeasure hμ),
    _root_.add_apply, thermalSignedInputMeasure, VectorMeasure.withDensity_apply hν,
    thermalSignedInputMeasure, VectorMeasure.withDensity_apply hμ,
    VectorMeasure.restrict_add]
  exact VectorMeasure.integral_add_vectorMeasure hν.restrict hμ.restrict

/-- Tilting the actual unit marker gives its literal positive thermal Dirac weight. -/
theorem thermalSignedInputMeasure_markerInput (b : ℝ) (hb : 0 ≤ b) (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    thermalSignedInputMeasure (markerInput b j) t =
      if j = 0 then VectorMeasure.dirac b (Real.exp (-t * b)) else 0 := by
  by_cases hj : j = 0
  · subst j
    ext s hs
    rw [thermalSignedInputMeasure_apply _ 0 b (markerInput_ae_physical b hb 0) ht]
    simp only [markerInput_zero, ite_true]
    rw [VectorMeasure.restrict_dirac hs]
    by_cases hbs : b ∈ s <;> simp [hbs, hs]
  · simp [markerInput, hj, thermalSignedInputMeasure]

/-- The actual canonical input has no row outside the selected finite spin family. -/
theorem canonicalMarkerReferenceInput_eq_zero_of_notMem (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) (hj : j ∉ lowBandSpinSet b) :
    canonicalMarkerReferenceInput a b ha hb j = 0 := by
  have h0 : (0 : ℤ) ∈ lowBandSpinSet b := by simpa using zero_lt_one.trans_le hb
  have hj0 : j ≠ 0 := fun h => hj (h ▸ h0)
  simp [canonicalMarkerReferenceInput, markerReferenceInput, markerInput,
    markerReferenceInverseInput, actualLocalAnchorInput, localAnchorInput,
    localAnchorHighInput, localInverseInput, hj, hj0]

/-- The actual tilted canonical input is its thermal marker plus its ordinary direct density. -/
theorem thermalSignedInputMeasure_canonicalMarkerReferenceInput (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    thermalSignedInputMeasure (canonicalMarkerReferenceInput a b ha hb j) t =
      (if j = 0 then VectorMeasure.dirac b (Real.exp (-t * b)) else 0) +
      (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
        canonicalMarkerReferenceDirectDensity a b ha hb j e) := by
  rw [canonicalMarkerReferenceInput_eq_marker_add_density,
    thermal_input_add _ _ t
      (signedIntegrable_thermalInput _ j b (markerInput_ae_physical b (zero_le_one.trans hb) j) ht)
      (signedDensity_integrable_thermal (canonicalMarkerReferenceDirectDensity_integrable a b ha hb j)
        (reference_ae_nonnegative j) ht.le),
    thermalSignedInputMeasure_markerInput b (zero_le_one.trans hb) j ht]
  congr 1
  exact signedDensity_withDensity_thermal
    (canonicalMarkerReferenceDirectDensity_integrable a b ha hb j)
    (reference_ae_nonnegative j) ht.le

private theorem canonical_continuum_eq_density (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (∑ J ∈ lowBandSpinSet b,
      correctedThermalContinuumMeasure (canonicalMarkerReferenceInput a b ha hb J) J j t) =
    (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
      (correctedSignedResponse
        (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) Subtype.val j e).re) := by
  ext s hs
  simp only [_root_.sum_apply]
  rw [withDensityᵥ_apply (integrable_finiteCorrectedThermalDensity (lowBandSpinSet b)
    (canonicalMarkerReferenceInput a b ha hb) j (3 * b)
    (fun J _ => canonicalMarkerReferenceInput_physicalSupport a b ha hb J) ht) hs]
  rw [Finset.sum_congr rfl (fun J hJ => correctedThermalContinuumMeasure_apply
    (canonicalMarkerReferenceInput a b ha hb J) J j (3 * b)
    (canonicalMarkerReferenceInput_physicalSupport a b ha hb J) ht s hs)]
  rw [← integral_finsetSum (lowBandSpinSet b) (fun J _ =>
    (integrable_correctedThermalRowDensity (canonicalMarkerReferenceInput a b ha hb J) J j
      (3 * b) (canonicalMarkerReferenceInput_physicalSupport a b ha hb J) ht).restrict)]
  apply integral_congr_ae
  filter_upwards with e
  simp only [correctedSignedResponse, Complex.re_sum, Finset.mul_sum, correctedThermalRowDensity]
  exact (Finset.sum_coe_sort (lowBandSpinSet b) (fun J => Real.exp (-t * e) *
    (correctedSignedRowResponse (canonicalMarkerReferenceInput a b ha hb J) J j e).re)).symm

/-- The complete actual ordinary output is exactly its scalar marker plus the
explicit vacuum, direct, and response density used by the pointwise estimates. -/
theorem canonicalMarkerReferenceThermalMeasure_eq_marker_add_density (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    canonicalMarkerReferenceThermalMeasure a b ha hb j t =
      (if j = 0 then VectorMeasure.dirac b (Real.exp (-t * b)) else 0) +
      (referenceMeasure j).withDensityᵥ (fun e => Real.exp (-t * e) *
        canonicalMarkerReferenceDensity a b ha hb j e) := by
  have hd := canonicalMarkerReferenceDirectDensity_thermal_integrable a b ha hb j ht
  have hv := integrable_vacuumThermalDensity a j ht
  have hc := integrable_finiteCorrectedThermalDensity (lowBandSpinSet b)
    (canonicalMarkerReferenceInput a b ha hb) j (3 * b)
    (fun J _ => canonicalMarkerReferenceInput_physicalSupport a b ha hb J) ht
  have hinput : (if j ∈ lowBandSpinSet b then
      thermalSignedInputMeasure (canonicalMarkerReferenceInput a b ha hb j) t else 0) =
      thermalSignedInputMeasure (canonicalMarkerReferenceInput a b ha hb j) t := by
    by_cases hj : j ∈ lowBandSpinSet b
    · simp [hj]
    · simp [hj, canonicalMarkerReferenceInput_eq_zero_of_notMem a b ha hb j hj,
        thermalSignedInputMeasure]
  change vacuumThermalContinuumMeasure a j t +
    ((if j ∈ lowBandSpinSet b then
      thermalSignedInputMeasure (canonicalMarkerReferenceInput a b ha hb j) t else 0) +
      ∑ J ∈ lowBandSpinSet b,
        correctedThermalContinuumMeasure (canonicalMarkerReferenceInput a b ha hb J) J j t) = _
  rw [hinput, thermalSignedInputMeasure_canonicalMarkerReferenceInput a b ha hb j ht,
    canonical_continuum_eq_density a b ha hb j ht]
  have hsplit : (fun e => Real.exp (-t * e) * canonicalMarkerReferenceDensity a b ha hb j e) =
      (fun e => Real.exp (-t * e) * canonicalMarkerReferenceDirectDensity a b ha hb j e) +
        (vacuumThermalDensity a j t + fun e => Real.exp (-t * e) *
          (correctedSignedResponse
            (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) Subtype.val j e).re) := by
    funext e
    simp only [Pi.add_apply, canonicalMarkerReferenceDensity, canonicalMarkerReferenceKernelNumerator,
      Analytic.vacuumNumerator, vacuumThermalDensity, mul_add]
  rw [hsplit, withDensityᵥ_add hd (hv.add hc), withDensityᵥ_add hv hc,
    vacuumThermalContinuumMeasure]
  abel

private theorem thermalDensity_ae_eq_zero_of_restrict_eq_zero
    (μ : Measure ℝ) (q : ℝ → ℝ) (b t : ℝ) (j : ℤ)
    (hq : Integrable (fun e => Real.exp (-t * e) * q e) μ)
    (hzero : ((if j = 0 then VectorMeasure.dirac b (Real.exp (-t * b)) else 0) +
      μ.withDensityᵥ (fun e => Real.exp (-t * e) * q e)).restrict (Iio b) = 0) :
    ∀ᵐ e ∂μ.restrict (Iio b), q e = 0 := by
  have hdirac : (if j = 0 then VectorMeasure.dirac b (Real.exp (-t * b)) else
      (0 : SignedMeasure ℝ)).restrict (Iio b) = 0 := by
    split_ifs
    · exact VectorMeasure.restrict_dirac_of_notMem (by simp)
    · simp
  rw [VectorMeasure.restrict_add, hdirac, zero_add] at hzero
  have hrestrict :
      (μ.withDensityᵥ (fun e => Real.exp (-t * e) * q e)).restrict (Iio b) =
        (μ.restrict (Iio b)).withDensityᵥ (fun e => Real.exp (-t * e) * q e) := by
    ext s hs
    rw [VectorMeasure.restrict_apply _ measurableSet_Iio hs,
      withDensityᵥ_apply hq (hs.inter measurableSet_Iio),
      withDensityᵥ_apply hq.restrict hs, Measure.restrict_restrict hs]
  rw [hrestrict] at hzero
  have hqzero := hq.restrict.ae_eq_of_withDensityᵥ_eq
    (integrable_zero ℝ ℝ (μ.restrict (Iio b)))
    (hzero.trans withDensityᵥ_zero.symm)
  filter_upwards [hqzero] with e he
  exact (mul_eq_zero.mp he).resolve_left (Real.exp_ne_zero _)

/-- The actual ordinary density vanishes almost everywhere below the cutoff;
this follows from the output measure gap and does not assume pointwise cancellation. -/
theorem canonicalMarkerReferenceDensity_ae_eq_zero_below_cutoff (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) :
    canonicalMarkerReferenceDensity a b ha hb j =ᵐ[(referenceMeasure j).restrict (Iio b)] 0 := by
  have hzero := canonicalMarkerReferenceThermalMeasure_restrict_below_cutoff a b ha hb j
    (t := 1) zero_lt_one
  rw [canonicalMarkerReferenceThermalMeasure_eq_marker_add_density a b ha hb j zero_lt_one] at hzero
  exact thermalDensity_ae_eq_zero_of_restrict_eq_zero (referenceMeasure j)
    (canonicalMarkerReferenceDensity a b ha hb j) b 1 j
    (canonicalMarkerReferenceDensity_thermal_integrable a b ha hb j zero_lt_one) hzero

end GapFamily.Construction
