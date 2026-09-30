import GapFamily.Construction.MarkerReferenceFiniteInverse
import GapFamily.Construction.MarkerReferenceMarker
import GapFamily.Analytic.Poincare.Repair.PoincareCanonicalLocalRepair

/-!
# The actual marker reference input

The unit scalar marker, actual vacuum-plus-marker inverse, and normalized
scalar anchor form one compact physical signed input. Its threshold is six,
exactly cancelling the vacuum threshold, and its ordinary low-band output is
the negative vacuum continuum.
-/

noncomputable section

open MeasureTheory Set

namespace GapFamily.Construction

open Analytic

variable (S : Finset ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 < b)
  (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))

/-- The exact scalar coefficient needed to cancel the vacuum and marker thresholds. -/
def markerReferenceAnchorCoefficient : ℝ :=
  7 - finiteSignedThresholdMass S (markerReferenceInverseInput S a b ha hb.le hunit)

/-- The literal marker-plus-inverse-plus-anchor ordinary signed input. -/
def markerReferenceInput : ℤ → SignedMeasure ℝ :=
  markerInput b + markerReferenceInverseInput S a b ha hb.le hunit +
    markerReferenceAnchorCoefficient S a b ha hb hunit • actualLocalAnchorInput S b hb hunit

private theorem marker_physicalSupport (b : ℝ) (hb : 0 < b) (j : ℤ) :
    ∀ᵐ E ∂(markerInput b j).variation, |(j : ℝ)| ≤ E ∧ E ≤ 3 * b :=
  (markerInput_ae_physical b hb.le j).mono (fun _ hE => ⟨hE.1, by linarith [hE.2]⟩)

/-- Every literal reference input measure is physically supported below `3b`. -/
theorem markerReferenceInput_physicalSupport :
    ∀ J ∈ S, ∀ᵐ E ∂(markerReferenceInput S a b ha hb hunit J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * b := by
  intro J _
  exact signedPhysicalSupport_add _ _ J (3 * b)
    (signedPhysicalSupport_add _ _ J (3 * b) (marker_physicalSupport b hb J)
      (markerReferenceInverseInput_ae_physical_le S a b ha hb.le hunit
        (3 * b) (by linarith) J))
    (signedPhysicalSupport_smul _ J (3 * b) _
      (actualLocalAnchorInput_physicalSupport S b hb hunit J))

/-- The ordinary inverse and anchor preserve exactly the original marker atom. -/
@[simp] theorem markerReferenceInput_singleton (j : ℤ) (e : ℝ) :
    markerReferenceInput S a b ha hb hunit j {e} = markerInput b j {e} := by
  simp [markerReferenceInput, markerReferenceInverseInput_singleton,
    actualLocalAnchorInput_singleton]

/-- The actual threshold is six, with no supplied normalization premise. -/
theorem markerReferenceInput_threshold (h0 : 0 ∈ S) :
    finiteSignedThresholdMass S (markerReferenceInput S a b ha hb hunit) = 6 := by
  simp only [markerReferenceInput, finiteSignedThresholdMass_add,
    finiteSignedThresholdMass_smul, finiteSignedThresholdMass_markerInput S h0 b,
    actualLocalAnchorInput_threshold_eq_one S h0 b hb hunit, mul_one,
    markerReferenceAnchorCoefficient]
  ring

/-- Vacuum threshold plus actual corrected reference threshold vanishes exactly. -/
theorem markerReferenceInput_total_threshold (h0 : 0 ∈ S) :
    -6 + finiteSignedThresholdMass S (markerReferenceInput S a b ha hb hunit) = 0 := by
  rw [markerReferenceInput_threshold S a b ha hb hunit h0]
  norm_num

/-- The ordinary signed vacuum continuum on an open physical low band. -/
def vacuumLowBandMeasure (a b : ℝ) (j : ℤ) : SignedMeasure ℝ :=
  ((referenceMeasure j).restrict (Ioo |(j : ℝ)| b)).withDensityᵥ
    (fun e => (vacuumFullKernel a e j).re)

theorem vacuumLowBandMeasure_apply (a b : ℝ) (j : ℤ) (ha : 2 ≤ a)
    (s : Set ℝ) (hs : MeasurableSet s) :
    vacuumLowBandMeasure a b j s = ∫ e in s, (vacuumFullKernel a e j).re
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b) :=
  withDensityᵥ_apply (vacuumFullKernel_lowBand_integrable a b j ha).re hs

private theorem markerColumn_add_source (a b : ℝ) (ha : 2 ≤ a) (hb : 0 < b) (j : ℤ) :
    ((referenceMeasure j).restrict (Ioo |(j : ℝ)| b)).withDensityᵥ
        (fun e => (correctedKernel j 0 e b).re) + markerReferenceSourceMeasure a b j =
      -vacuumLowBandMeasure a b j := by
  have hi : Integrable (fun e => (correctedKernel j 0 e b).re)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| b)) := by
    have h := ((markerReferenceRhs_integrable a b j ha hb.le).neg.sub
      (vacuumFullKernel_lowBand_integrable a b j ha)).re
    convert h using 1
    funext e
    simp [markerReferenceRhs]
  apply VectorMeasure.ext
  intro s hs
  have hsour : Integrable (fun e => (markerReferenceRhs a b j e).re)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| b)) :=
    (markerReferenceRhs_integrable a b j ha hb.le).re
  rw [_root_.add_apply, withDensityᵥ_apply hi hs,
    markerReferenceSourceMeasure_apply a b j ha hb.le s hs, _root_.neg_apply,
    vacuumLowBandMeasure_apply a b j ha s hs,
    ← integral_add hi.integrableOn hsour.integrableOn, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with e
  simp [markerReferenceRhs]

/-- The literal reference input cancels the entire ordinary vacuum low-band continuum. -/
theorem markerReferenceInput_lowBandOutput (h0 : 0 ∈ S) (j : ℤ) (hj : j ∈ S) :
    finiteCorrectedLowBandOutput S (markerReferenceInput S a b ha hb hunit)
      j (3 * b) b (markerReferenceInput_physicalSupport S a b ha hb hunit) =
      -vacuumLowBandMeasure a b j := by
  let μ := markerReferenceInverseInput S a b ha hb.le hunit
  let θ := actualLocalAnchorInput S b hb hunit
  let t := markerReferenceAnchorCoefficient S a b ha hb hunit
  have hm : ∀ J ∈ S, ∀ᵐ E ∂(markerInput b J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * b := fun J _ => marker_physicalSupport b hb J
  have hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * b :=
    fun J _ => markerReferenceInverseInput_ae_physical_le S a b ha hb.le hunit
      (3 * b) (by linarith) J
  have hθ : ∀ J ∈ S, ∀ᵐ E ∂(θ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * b :=
    fun J _ => actualLocalAnchorInput_physicalSupport S b hb hunit J
  have hmμ : ∀ J ∈ S, ∀ᵐ E ∂(markerInput b J + μ J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * b :=
    fun J hJ => signedPhysicalSupport_add _ _ J (3 * b) (hm J hJ) (hμ J hJ)
  have htθ : ∀ J ∈ S, ∀ᵐ E ∂(t • θ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * b :=
    fun J hJ => signedPhysicalSupport_smul _ J (3 * b) t (hθ J hJ)
  change finiteCorrectedLowBandOutput S (fun J => (markerInput b J + μ J) + t • θ J)
    j (3 * b) b _ = _
  rw [finiteCorrectedLowBandOutput_add S (fun J => markerInput b J + μ J)
      (fun J => t • θ J) j (3 * b) b hmμ htθ,
    finiteCorrectedLowBandOutput_add S (markerInput b) μ j (3 * b) b hm hμ,
    finiteCorrectedLowBandOutput_smul S θ t j (3 * b) b hθ]
  rw [actualLocalAnchorInput_lowBandOutput S b hb hunit j hj, smul_zero, add_zero]
  rw [finiteCorrectedLowBandOutput_markerReferenceInverseInput_of_le
    S a b ha hb.le hunit (3 * b) (by linarith) j hj]
  rw [finiteCorrectedLowBandOutput_inputCutoff_eq S (markerInput b) j (3 * b) b b hm
    (fun J _ => markerInput_ae_physical b hb.le J),
    finiteCorrectedLowBandOutput_markerInput S h0 b hb.le j]
  exact markerColumn_add_source a b ha hb j

/-- Vacuum continuum plus the actual corrected reference output is the zero signed measure. -/
theorem vacuumLowBandMeasure_add_markerReferenceInput_output
    (h0 : 0 ∈ S) (j : ℤ) (hj : j ∈ S) :
    vacuumLowBandMeasure a b j +
      finiteCorrectedLowBandOutput S (markerReferenceInput S a b ha hb hunit)
        j (3 * b) b (markerReferenceInput_physicalSupport S a b ha hb hunit) = 0 := by
  rw [markerReferenceInput_lowBandOutput S a b ha hb hunit h0 j hj, add_neg_cancel]

end GapFamily.Construction
