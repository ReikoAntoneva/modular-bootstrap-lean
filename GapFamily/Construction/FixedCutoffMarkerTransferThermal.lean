import GapFamily.Construction.FixedCutoffMarkerTransfer
import GapFamily.Construction.MarkerReferenceDensityOutput
import GapFamily.Construction.CellThermalReplacement

/-! Literal thermal measures for fixed-cutoff marker transfer. The endpoint
marker at zero comes from the scalar threshold coefficient, so the combined
output has the same uniform Dirac formula throughout the closed gap interval.
-/

noncomputable section
namespace GapFamily.Construction

open MeasureTheory Set Analytic
open scoped Classical

/-- Thermal tilting of the positive-gap seed inserts precisely its positive
marker, and vanishes at the threshold endpoint. -/
theorem thermalSignedInputMeasure_positiveGapMarkerInput (δ : ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    thermalSignedInputMeasure (positiveGapMarkerInput δ j) t =
      if 0 < δ ∧ j = 0 then VectorMeasure.dirac δ (Real.exp (-t * δ)) else 0 := by
  by_cases hδ : 0 < δ
  · rw [positiveGapMarkerInput_of_pos hδ,
      thermalSignedInputMeasure_markerInput δ hδ.le j ht]
    simp [hδ]
  · simp [positiveGapMarkerInput, hδ, thermalSignedInputMeasure]

/-- The whole ordinary thermal transfer is the difference of its two
literal weighted markers. The new marker is absent as an input at zero. -/
theorem thermalSignedInputMeasure_fixedCutoffMarkerTransfer (B δ : ℝ)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    thermalSignedInputMeasure (fixedCutoffMarkerTransfer B δ j) t =
      (if 0 < δ ∧ j = 0 then VectorMeasure.dirac δ (Real.exp (-t * δ)) else 0) -
        (if j = 0 then VectorMeasure.dirac B (Real.exp (-t * B)) else 0) := by
  have hpositive : (positiveGapMarkerInput δ j).Integrable (fun E => Real.exp (-t * E)) := by
    by_cases hpos : 0 < δ
    · rw [positiveGapMarkerInput_of_pos hpos]
      exact signedIntegrable_thermalInput _ j δ (markerInput_ae_physical δ hδ j) ht
    · simp [positiveGapMarkerInput, hpos]
  have hold := signedIntegrable_thermalInput _ j B
    (markerInput_ae_physical B (hδ.trans hδB) j) ht
  change thermalSignedInputMeasure (positiveGapMarkerInput δ j - markerInput B j) t = _
  rw [thermalSignedInputMeasure_sub_of_integrable _ _ t hpositive hold,
    thermalSignedInputMeasure_positiveGapMarkerInput δ j ht,
    thermalSignedInputMeasure_markerInput B (hδ.trans hδB) j ht]

/-- Combining the ordinary transfer with its scalar threshold recovers the
unit weighted marker at every nonnegative prescribed energy, including zero. -/
theorem fixedCutoffMarkerTransfer_thermal_with_threshold
    (S : Finset ℤ) (h0 : 0 ∈ S) (B δ : ℝ)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    thermalSignedInputMeasure (fixedCutoffMarkerTransfer B δ j) t +
      (if j = 0 then VectorMeasure.dirac (0 : ℝ)
        (finiteSignedThresholdMass S (fixedCutoffMarkerTransfer B δ)) else 0) =
      (if j = 0 then VectorMeasure.dirac δ (Real.exp (-t * δ)) else 0) -
        (if j = 0 then VectorMeasure.dirac B (Real.exp (-t * B)) else 0) := by
  rw [thermalSignedInputMeasure_fixedCutoffMarkerTransfer B δ hδ hδB j ht,
    fixedCutoffMarkerTransfer_threshold S h0 B δ hδ]
  by_cases hzero : δ = 0
  · subst δ
    by_cases hj : j = 0 <;> simp [hj, sub_eq_add_neg, add_comm]
  · have hpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hzero)
    by_cases hj : j = 0 <;> simp [hj, hzero, hpos]

end GapFamily.Construction
