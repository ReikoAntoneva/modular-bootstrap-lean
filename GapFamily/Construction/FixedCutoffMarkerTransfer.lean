import GapFamily.Construction.MarkerReferenceMarker
import GapFamily.Analytic.Foundation.SignedPhysicalSupport
import GapFamily.Analytic.Poincare.Repair.PoincareLocalAnchorVariation

/-!
# Marker transfer at a fixed cutoff

The inherited reference has its marker at `B`. The signed input below moves
that marker to a prescribed `δ ∈ [0,B)`. At `δ = 0` there is no origin input:
removing the old marker has threshold coefficient one, which the exact local
repair preserves. Thus the endpoint is a genuine threshold output atom.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace GapFamily.Construction

open Analytic

/-- Only a strictly positive prescribed energy is inserted as an ordinary seed. -/
def positiveGapMarkerInput (δ : ℝ) : ℤ → SignedMeasure ℝ :=
  if 0 < δ then markerInput δ else 0

/-- Removing the old marker and inserting the positive prescribed marker. -/
def fixedCutoffMarkerTransfer (B δ : ℝ) : ℤ → SignedMeasure ℝ :=
  positiveGapMarkerInput δ - markerInput B

@[simp] theorem positiveGapMarkerInput_zero : positiveGapMarkerInput 0 = 0 := by
  simp [positiveGapMarkerInput]

@[simp] theorem positiveGapMarkerInput_of_pos {δ : ℝ} (hδ : 0 < δ) :
    positiveGapMarkerInput δ = markerInput δ := by
  simp [positiveGapMarkerInput, hδ]

/-- No origin atom enters the ordinary signed seed, including at `δ = 0`. -/
theorem positiveGapMarkerInput_origin (δ : ℝ) (j : ℤ) :
    positiveGapMarkerInput δ j {0} = 0 := by
  by_cases hδ : 0 < δ
  · simp [positiveGapMarkerInput, hδ, markerInput_singleton, ne_of_lt hδ]
  · simp [positiveGapMarkerInput, hδ]

@[simp] theorem fixedCutoffMarkerTransfer_singleton (B δ : ℝ) (j : ℤ) (e : ℝ) :
    fixedCutoffMarkerTransfer B δ j {e} =
      (if 0 < δ ∧ j = 0 ∧ e = δ then 1 else 0) -
        (if j = 0 ∧ e = B then 1 else 0) := by
  by_cases hδ : 0 < δ <;>
    simp [fixedCutoffMarkerTransfer, positiveGapMarkerInput, hδ, markerInput_singleton]

/-- The physical support bound is independent of the prescribed marker position. -/
theorem fixedCutoffMarkerTransfer_physicalSupport (B δ : ℝ)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) (j : ℤ) :
    ∀ᵐ E ∂(fixedCutoffMarkerTransfer B δ j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ B := by
  apply signedPhysicalSupport_sub _ _ j B
  · by_cases hpos : 0 < δ
    · simpa only [positiveGapMarkerInput_of_pos hpos] using
        (markerInput_ae_physical δ hδ j).mono (fun _ h => ⟨h.1, h.2.trans hδB⟩)
    · simp [positiveGapMarkerInput, hpos]
  · exact markerInput_ae_physical B (hδ.trans hδB) j

/-- The correction contains no scalar origin input when the old cutoff is positive. -/
theorem fixedCutoffMarkerTransfer_origin (B δ : ℝ) (hB : 0 < B) (j : ℤ) :
    fixedCutoffMarkerTransfer B δ j {0} = 0 := by
  simp [fixedCutoffMarkerTransfer, positiveGapMarkerInput_origin, markerInput_singleton,
    ne_of_lt hB]

/-- Exact scalar threshold: the unit threshold is retained precisely at `δ = 0`. -/
theorem fixedCutoffMarkerTransfer_threshold (S : Finset ℤ) (h0 : 0 ∈ S)
    (B δ : ℝ) (hδ : 0 ≤ δ) :
    finiteSignedThresholdMass S (fixedCutoffMarkerTransfer B δ) =
      if δ = 0 then 1 else 0 := by
  rw [fixedCutoffMarkerTransfer, finiteSignedThresholdMass_sub]
  by_cases hzero : δ = 0
  · simp [hzero, finiteSignedThresholdMass_markerInput S h0]
  · have hpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hzero)
    simp [positiveGapMarkerInput_of_pos hpos,
      finiteSignedThresholdMass_markerInput S h0, hzero]

/-- Each row has at most two units of ordinary variation, uniformly in `δ`. -/
theorem fixedCutoffMarkerTransfer_variation_le (B δ : ℝ) (j : ℤ) :
    (fixedCutoffMarkerTransfer B δ j).variation.real univ ≤
      if j = 0 then 2 else 0 := by
  have h := signedMeasure_variation_real_sub_le
    (positiveGapMarkerInput δ j) (markerInput B j)
  change (positiveGapMarkerInput δ j - markerInput B j).variation.real univ ≤ _
  apply h.trans
  by_cases hδ : 0 < δ <;> by_cases hj : j = 0 <;>
    norm_num [positiveGapMarkerInput, hδ, markerInput_totalVariation, hj]

/-- The total ordinary variation has a single bound for every marker in the band. -/
theorem fixedCutoffMarkerTransfer_totalVariation_le (S : Finset ℤ) (h0 : 0 ∈ S)
    (B δ : ℝ) :
    (∑ j ∈ S, (fixedCutoffMarkerTransfer B δ j).variation.real univ) ≤ 2 := by
  calc
    _ ≤ ∑ j ∈ S, if j = 0 then (2 : ℝ) else 0 :=
      Finset.sum_le_sum fun j _ => fixedCutoffMarkerTransfer_variation_le B δ j
    _ = 2 := by simp [h0]

end GapFamily.Construction
