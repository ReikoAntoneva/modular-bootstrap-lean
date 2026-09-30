import GapFamily.Construction.MarkerReferenceThermalMeasure
import GapFamily.Construction.MarkerReferenceCanonical
import GapFamily.Analytic.Foundation.SignedBandRestriction

/-!
# Complete support of the actual marker reference output

Open-band cancellation, physical support below the spin edge, and the exact
atom formula give vanishing on the entire lower interval. This is an identity
of ordinary signed measures and therefore also controls their total variation.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace GapFamily.Construction

open Analytic
open PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier

variable (S : Finset ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 < b)
  (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))

/-- Omitting the scalar threshold leaves the physical lower support unchanged. -/
theorem markerReferenceNonthresholdOutput_restrict_below_edge (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (markerReferenceNonthresholdOutput S a b ha hb hunit j t).restrict (Iio |(j : ℝ)|) = 0 := by
  have h := correctedThermalFiniteOutputMeasure_restrict_below_edge S
    (markerReferenceInput S a b ha hb hunit) j (3 * b)
    (markerReferenceInput_physicalSupport S a b ha hb hunit) ht
  have hth :
      (if j = 0 then VectorMeasure.dirac (0 : ℝ)
        (finiteSignedThresholdMass S (markerReferenceInput S a b ha hb hunit)) else 0).restrict
          (Iio |(j : ℝ)|) = 0 := by
    by_cases hj : j = 0
    · subst j
      simp only [ite_true, Int.cast_zero, abs_zero]
      exact VectorMeasure.restrict_dirac_of_notMem (by simp)
    · simp [hj]
  rw [correctedThermalFiniteOutputMeasure_eq, VectorMeasure.restrict_add, hth, add_zero] at h
  exact h

/-- The full vacuum continuum has no signed measure below its physical spin edge. -/
theorem vacuumThermalContinuumMeasure_restrict_below_edge (a : ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (vacuumThermalContinuumMeasure a j t).restrict (Iio |(j : ℝ)|) = 0 := by
  ext s hs
  rw [VectorMeasure.restrict_apply _ measurableSet_Iio hs, _root_.zero_apply]
  exact vacuumThermalContinuumMeasure_apply_eq_zero_below_edge a j ht _
    (hs.inter measurableSet_Iio) (by
      intro E hE
      change E ≤ |(j : ℝ)|
      exact hE.2.le)

/-- The complete vacuum-plus-reference output vanishes strictly below its physical spin edge. -/
theorem markerReferenceThermalMeasure_restrict_below_edge (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (markerReferenceThermalMeasure S a b ha hb hunit j t).restrict (Iio |(j : ℝ)|) = 0 := by
  rw [markerReferenceThermalMeasure, VectorMeasure.restrict_add,
    vacuumThermalContinuumMeasure_restrict_below_edge a j ht,
    markerReferenceNonthresholdOutput_restrict_below_edge S a b ha hb hunit j ht, add_zero]

/-- The full actual variation is carried by the physical energy cone. -/
theorem markerReferenceThermalMeasure_ae_physical (j : ℤ) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ E ∂(markerReferenceThermalMeasure S a b ha hb hunit j t).variation, |(j : ℝ)| ≤ E := by
  have hr : (markerReferenceThermalMeasure S a b ha hb hunit j t).variation.restrict
      (Iio |(j : ℝ)|) = 0 := by
    rw [← VectorMeasure.variation_restrict measurableSet_Iio,
      markerReferenceThermalMeasure_restrict_below_edge S a b ha hb hunit j ht,
      VectorMeasure.variation_zero]
  have hzero := Measure.restrict_eq_zero.mp hr
  exact (measure_eq_zero_iff_ae_notMem.mp hzero).mono fun _ hE => le_of_not_gt hE

/-- No physical-edge atom remains, including at the scalar origin. -/
theorem markerReferenceThermalMeasure_edge_atom (h0 : 0 ∈ S) (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    markerReferenceThermalMeasure S a b ha hb hunit j t {|(j : ℝ)|} = 0 := by
  rw [markerReferenceThermalMeasure_singleton S a b ha hb hunit h0 j ht]
  by_cases hj : j = 0 <;> simp [hj, hb.ne]

/-- Cancellation on a selected open row extends to the complete interval below the cutoff. -/
theorem markerReferenceThermalMeasure_restrict_below_cutoff (h0 : 0 ∈ S)
    (j : ℤ) (hj : j ∈ S) {t : ℝ} (ht : 0 < t) :
    (markerReferenceThermalMeasure S a b ha hb hunit j t).restrict (Iio b) = 0 := by
  suffices h : (markerReferenceThermalMeasure S a b ha hb hunit j t).restrict (Iio b) =
      (0 : SignedMeasure ℝ).restrict (Iio b) by simpa using h
  apply signedMeasure_restrict_Iio_eq_of_physical_band _ _ |(j : ℝ)| b
  · exact markerReferenceThermalMeasure_restrict_below_edge S a b ha hb hunit j ht
  · simp
  · simpa only [VectorMeasure.restrict_zero] using
      markerReferenceThermalMeasure_restrict_openLowBand S a b ha hb hunit h0 j hj ht
  · simpa only [_root_.zero_apply] using
      markerReferenceThermalMeasure_edge_atom S a b ha hb hunit h0 j ht

/-- Covering all physical low spins removes the complete lower interval in every integer row. -/
theorem markerReferenceThermalMeasure_restrict_below_cutoff_of_cover (h0 : 0 ∈ S)
    (hcover : ∀ j : ℤ, |(j : ℝ)| < b → j ∈ S) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (markerReferenceThermalMeasure S a b ha hb hunit j t).restrict (Iio b) = 0 := by
  by_cases hj : |(j : ℝ)| < b
  · exact markerReferenceThermalMeasure_restrict_below_cutoff S a b ha hb hunit h0 j
      (hcover j hj) ht
  · have h := congrArg (fun ν : SignedMeasure ℝ => ν.restrict (Iio b))
      (markerReferenceThermalMeasure_restrict_below_edge S a b ha hb hunit j ht)
    have hinter : Iio b ∩ Iio |(j : ℝ)| = Iio b :=
      inter_eq_left.mpr (Iio_subset_Iio (le_of_not_gt hj))
    simpa only [VectorMeasure.restrict_restrict _ measurableSet_Iio measurableSet_Iio,
      hinter, VectorMeasure.restrict_zero] using h

/-- The ordinary total variation, rather than only signed mass, is carried above the cutoff. -/
theorem markerReferenceThermalMeasure_ae_ge_cutoff (h0 : 0 ∈ S)
    (hcover : ∀ j : ℤ, |(j : ℝ)| < b → j ∈ S) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ E ∂(markerReferenceThermalMeasure S a b ha hb hunit j t).variation, b ≤ E := by
  have hr : (markerReferenceThermalMeasure S a b ha hb hunit j t).variation.restrict
      (Iio b) = 0 := by
    rw [← VectorMeasure.variation_restrict measurableSet_Iio,
      markerReferenceThermalMeasure_restrict_below_cutoff_of_cover S a b ha hb hunit h0 hcover j ht,
      VectorMeasure.variation_zero]
  have hzero := Measure.restrict_eq_zero.mp hr
  exact (measure_eq_zero_iff_ae_notMem.mp hzero).mono fun _ hE => le_of_not_gt hE

/-- The literal complete ordinary output for the canonical set of physical low spins. -/
def canonicalMarkerReferenceThermalMeasure (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  markerReferenceThermalMeasure (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb) j t

/-- The canonical actual output vanishes below its cutoff, in every integer spin. -/
theorem canonicalMarkerReferenceThermalMeasure_restrict_below_cutoff
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (canonicalMarkerReferenceThermalMeasure a b ha hb j t).restrict (Iio b) = 0 :=
  markerReferenceThermalMeasure_restrict_below_cutoff_of_cover (lowBandSpinSet b) a b ha
    (by linarith) (isUnit_correctedLowBandIdentityPlus_canonical b hb)
    (by simpa using zero_lt_one.trans_le hb) (fun j hj => (mem_lowBandSpinSet b j).mpr hj) j ht

/-- The gap of the canonical ordinary output holds for its actual total variation. -/
theorem canonicalMarkerReferenceThermalMeasure_ae_ge_cutoff
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ E ∂(canonicalMarkerReferenceThermalMeasure a b ha hb j t).variation, b ≤ E :=
  markerReferenceThermalMeasure_ae_ge_cutoff (lowBandSpinSet b) a b ha
    (by linarith) (isUnit_correctedLowBandIdentityPlus_canonical b hb)
    (by simpa using zero_lt_one.trans_le hb) (fun j hj => (mem_lowBandSpinSet b j).mpr hj) j ht

/-- The canonical output variation obeys both the cutoff gap and the physical spin edge. -/
theorem canonicalMarkerReferenceThermalMeasure_ae_ge_max
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ E ∂(canonicalMarkerReferenceThermalMeasure a b ha hb j t).variation,
      max b |(j : ℝ)| ≤ E := by
  have hphys := markerReferenceThermalMeasure_ae_physical (lowBandSpinSet b) a b ha
    (by linarith) (isUnit_correctedLowBandIdentityPlus_canonical b hb) j ht
  filter_upwards [canonicalMarkerReferenceThermalMeasure_ae_ge_cutoff a b ha hb j ht, hphys]
    with E hcut hcone
  exact max_le hcut hcone

/-- The only atom in the full canonical ordinary output is the scalar unit marker. -/
theorem canonicalMarkerReferenceThermalMeasure_singleton
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    canonicalMarkerReferenceThermalMeasure a b ha hb j t {e} =
      if j = 0 ∧ e = b then Real.exp (-t * e) else 0 :=
  markerReferenceThermalMeasure_singleton (lowBandSpinSet b) a b ha
    (by linarith) (isUnit_correctedLowBandIdentityPlus_canonical b hb)
    (by simpa using zero_lt_one.trans_le hb) j ht e

/-- The canonical Fourier coefficient is the mass of the same actual measure
whose complete support gap was proved above. -/
theorem canonicalMarkerReferenceOutputCoefficient_eq_thermalMass
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (y : ℝ) (hy : 0 < y) (j : ℤ) :
    canonicalMarkerReferenceOutputCoefficient a b ha hb y j =
      (Real.sqrt y : ℂ) *
        (canonicalMarkerReferenceThermalMeasure a b ha hb j (2 * Real.pi * y) univ : ℂ) :=
  markerReferenceOutputCoefficient_eq_thermalMass (lowBandSpinSet b) a b ha
    (by linarith) (isUnit_correctedLowBandIdentityPlus_canonical b hb) y hy j

/-- The actual canonical modular seed is reconstructed from the ordinary
measure family carrying the proved cutoff gap and unit scalar marker. -/
theorem hasSum_canonicalMarkerReferenceSeed_thermalMeasure
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (canonicalMarkerReferenceThermalMeasure a b ha hb j (2 * Real.pi * y) univ : ℂ) *
        cuspFourierMode j x)
      (canonicalMarkerReferenceSeed a b ha hb (rowPoint y hy x) - vacuumDirectRow a y x) :=
  hasSum_markerReferenceSeed_thermalMeasure (lowBandSpinSet b) a b ha
    (by linarith) (isUnit_correctedLowBandIdentityPlus_canonical b hb)
    (by simpa using zero_lt_one.trans_le hb) y hy x

end GapFamily.Construction
