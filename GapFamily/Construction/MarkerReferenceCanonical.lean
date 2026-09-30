import GapFamily.Construction.MarkerReferenceSeed
import GapFamily.Analytic.Kernel.FullKernelInverse

/-!
# The canonical actual marker reference

The row set is exactly the integer spins meeting the open physical low band.
The proved full inverse and actual normalized anchor discharge all inverse
and anchor hypotheses in the reference construction.
-/

noncomputable section

open MeasureTheory Set UpperHalfPlane
open scoped BigOperators MatrixGroups

namespace GapFamily.Construction

open Analytic PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier

/-- The literal reference input on every physical integer row meeting the low band. -/
def canonicalMarkerReferenceInput (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    ℤ → SignedMeasure ℝ :=
  markerReferenceInput (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb)

/-- Every actual reference input row has compact physical variation support. -/
theorem canonicalMarkerReferenceInput_physicalSupport (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) :
    ∀ᵐ E ∂(canonicalMarkerReferenceInput a b ha hb j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ 3 * b := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  unfold canonicalMarkerReferenceInput markerReferenceInput
  apply signedPhysicalSupport_add _ _ j (3 * b)
  · apply signedPhysicalSupport_add _ _ j (3 * b)
    · exact (markerInput_ae_physical b hb0 j).mono
        (fun _ hE => ⟨hE.1, by linarith [hE.2]⟩)
    · exact markerReferenceInverseInput_ae_physical_le (lowBandSpinSet b) a b ha hb0
        (isUnit_correctedLowBandIdentityPlus_canonical b hb) (3 * b) (by linarith) j
  · exact signedPhysicalSupport_smul _ j (3 * b) _
      (actualLocalAnchorInput_physicalSupport (lowBandSpinSet b) b hbpos
        (isUnit_correctedLowBandIdentityPlus_canonical b hb) j)

/-- The actual inverse and continuous anchor introduce no atom besides the unit marker. -/
@[simp] theorem canonicalMarkerReferenceInput_singleton (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) (e : ℝ) :
    canonicalMarkerReferenceInput a b ha hb j {e} =
      if j = 0 ∧ e = b then 1 else 0 := by
  rw [canonicalMarkerReferenceInput, markerReferenceInput_singleton, markerInput_singleton]

/-- The constructed correction cancels the vacuum's scalar threshold coefficient. -/
theorem canonicalMarkerReferenceInput_threshold (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    finiteSignedThresholdMass (lowBandSpinSet b) (canonicalMarkerReferenceInput a b ha hb) = 6 :=
  markerReferenceInput_threshold (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb) (by simpa using zero_lt_one.trans_le hb)

theorem canonicalMarkerReferenceInput_total_threshold (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    -6 + finiteSignedThresholdMass (lowBandSpinSet b) (canonicalMarkerReferenceInput a b ha hb) = 0 := by
  rw [canonicalMarkerReferenceInput_threshold]
  norm_num

/-- Every physical spin below the cutoff has exactly the negative vacuum continuum output. -/
theorem canonicalMarkerReferenceInput_lowBandOutput (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) (hj : |(j : ℝ)| < b) :
    finiteCorrectedLowBandOutput (lowBandSpinSet b) (canonicalMarkerReferenceInput a b ha hb)
      j (3 * b) b (fun J _ => canonicalMarkerReferenceInput_physicalSupport a b ha hb J) =
      -vacuumLowBandMeasure a b j :=
  markerReferenceInput_lowBandOutput (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb)
    (by simpa using zero_lt_one.trans_le hb) j ((mem_lowBandSpinSet b j).mpr hj)

/-- The complete ordinary vacuum-plus-reference continuum vanishes on every low-band row. -/
theorem vacuumLowBandMeasure_add_canonicalMarkerReferenceInput_output (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) (hj : |(j : ℝ)| < b) :
    vacuumLowBandMeasure a b j +
      finiteCorrectedLowBandOutput (lowBandSpinSet b) (canonicalMarkerReferenceInput a b ha hb)
        j (3 * b) b (fun J _ => canonicalMarkerReferenceInput_physicalSupport a b ha hb J) = 0 := by
  rw [canonicalMarkerReferenceInput_lowBandOutput a b ha hb j hj, add_neg_cancel]

/-- The actual canonical modular reference function. -/
def canonicalMarkerReferenceSeed (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) : UpperHalfPlane → ℂ :=
  markerReferenceSeed (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb)

/-- The canonical reference function has actual modular invariance. -/
theorem canonicalMarkerReferenceSeed_smul (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    canonicalMarkerReferenceSeed a b ha hb (g • τ) = canonicalMarkerReferenceSeed a b ha hb τ :=
  markerReferenceSeed_smul (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb) τ g

theorem continuous_canonicalMarkerReferenceSeed (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    Continuous (canonicalMarkerReferenceSeed a b ha hb) :=
  continuous_markerReferenceSeed (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb)

/-- The actual ordinary reference output after scalar-threshold cancellation. -/
def canonicalMarkerReferenceNonthresholdOutput (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  markerReferenceNonthresholdOutput (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb) j t

/-- Its only remaining point mass is the prescribed thermally weighted unit marker. -/
theorem canonicalMarkerReferenceNonthresholdOutput_singleton (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    canonicalMarkerReferenceNonthresholdOutput a b ha hb j t {e} =
      if j = 0 ∧ e = b then Real.exp (-t * e) else 0 :=
  markerReferenceNonthresholdOutput_singleton (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb)
    (by simpa using zero_lt_one.trans_le hb) j ht e

/-- The actual signed correction preserves every negative-energy vacuum measure. -/
theorem canonicalMarkerReferenceThermalOutput_preserves_vacuum (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (V : SignedMeasure ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (V + correctedThermalFiniteOutputMeasure (lowBandSpinSet b)
      (canonicalMarkerReferenceInput a b ha hb) j t).restrict (Iio (0 : ℝ)) =
      V.restrict (Iio (0 : ℝ)) :=
  markerReferenceThermalOutput_preserves_vacuum (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb) V j ht

/-- The ordinary output coefficient of the actual canonical reference. -/
def canonicalMarkerReferenceOutputCoefficient (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (y : ℝ) (j : ℤ) : ℂ :=
  markerReferenceOutputCoefficient (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb) y j

/-- The ordinary Fourier–Laplace output converges to the actual modular reference. -/
theorem hasSum_canonicalMarkerReferenceSeed_output (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => canonicalMarkerReferenceOutputCoefficient a b ha hb y j *
      cuspFourierMode j x)
      (canonicalMarkerReferenceSeed a b ha hb (rowPoint y hy x) - vacuumDirectRow a y x) :=
  hasSum_markerReferenceSeed_output (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb)
    (by simpa using zero_lt_one.trans_le hb) y hy x

theorem summable_norm_canonicalMarkerReferenceSeed_output (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    Summable (fun j : ℤ => ‖canonicalMarkerReferenceOutputCoefficient a b ha hb y j *
      cuspFourierMode j x‖) :=
  (hasSum_canonicalMarkerReferenceSeed_output a b ha hb y hy x).summable.norm

/-- The actual modular function equals its prescribed direct vacuum and complete ordinary output. -/
theorem canonicalMarkerReferenceSeed_eq_full_output (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    canonicalMarkerReferenceSeed a b ha hb (rowPoint y hy x) = vacuumDirectRow a y x +
      ∑' j : ℤ, canonicalMarkerReferenceOutputCoefficient a b ha hb y j * cuspFourierMode j x :=
  markerReferenceSeed_eq_full_output (lowBandSpinSet b) a b ha (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb)
    (by simpa using zero_lt_one.trans_le hb) y hy x

/-- At the physical shift the direct term is exactly the specified single vacuum character. -/
theorem canonicalMarkerReferenceSeed_eq_character_output (b : ℝ) (hb : 1 ≤ b)
    (c : ℝ) (hc : 2 ≤ GapFamily.shift c) (τ : UpperHalfPlane) :
    canonicalMarkerReferenceSeed (GapFamily.shift c) b hc hb τ =
      (Real.sqrt τ.im : ℂ) * GapFamily.vacuumNumerator c τ +
        ∑' j : ℤ, canonicalMarkerReferenceOutputCoefficient (GapFamily.shift c) b hc hb τ.im j *
          cuspFourierMode j τ.re :=
  markerReferenceSeed_eq_character_output (lowBandSpinSet b) b (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb) c hc
    (by simpa using zero_lt_one.trans_le hb) τ

end GapFamily.Construction
