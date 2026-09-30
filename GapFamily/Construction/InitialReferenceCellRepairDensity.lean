import GapFamily.Construction.InitialReferenceCellRepairDatum
import GapFamily.Construction.SignedMeasureCutoffPartition
import GapFamily.Analytic.Poincare.Repair.PoincareExteriorMeasureOutput
import GapFamily.Analytic.Poincare.Repair.PoincareSingleSpinRepair

/-! The full ordinary thermal output of an actual initial reference cell
repair consists of its single-row residual and the genuine exterior kernel
numerator. -/

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace GapFamily.Construction
open Analytic

private theorem restricted_density_eq_indicator (μ : Measure ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) (f : ℝ → ℝ) (hf : Integrable f (μ.restrict s)) :
    (μ.restrict s).withDensityᵥ f = μ.withDensityᵥ (s.indicator f) := by
  ext t ht
  rw [withDensityᵥ_apply hf ht,
    withDensityᵥ_apply ((integrable_indicator_iff hs).mpr hf) ht,
    setIntegral_indicator hs, Measure.restrict_restrict ht]

namespace InitialReferenceCell
variable {J : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
  (cell : InitialReferenceCell J L U k q) (B : ℝ) (hB : 1 ≤ B)

/-- The actual exterior numerator of the repair, obtained by integrating its
entire input kernel against this cell's literal single-row residual. -/
def exteriorNumerator (j : ℤ) (e : ℝ) : ℝ :=
  (canonicalRepairExteriorNumerator cell.rowInput B hB j e).re

variable (hJ : |(J : ℝ)| ≤ L) (hcut : cell.right < B)
include hJ hcut

/-- Only the actual cell row contributes to the signed kernel superposition. -/
theorem exteriorNumerator_eq_signed_integral (j : ℤ) (e : ℝ) :
    cell.exteriorNumerator B hB j e =
      (∫ᵛ E, canonicalRepairKernelEnergy B hB j J e E ∂<•cell.residual).re := by
  exact congrArg Complex.re
    (canonicalRepairExteriorNumerator_singleSpin J cell.residual B hB
      (cell.input_spin_mem B hJ hcut) j e)

/-- The genuine exterior numerator has an ordinary absolutely convergent
thermal integral against the physical reference measure. -/
theorem integrable_exteriorNumerator_thermal (j : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun e => Real.exp (-t * e) * cell.exteriorNumerator B hB j e)
      (referenceMeasure j) :=
  integrable_canonicalRepairExteriorNumerator_thermal cell.rowInput B hB
    (cell.rowInput_physicalSupport B hB hJ hcut) j ht

/-- The literal exterior indicator retains ordinary thermal integrability. -/
theorem integrable_exteriorNumerator_indicator_thermal (j : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun e => if B < e then
      Real.exp (-t * e) * cell.exteriorNumerator B hB j e else 0) (referenceMeasure j) := by
  simpa only [Set.indicator, Set.mem_Ioi] using!
    (cell.integrable_exteriorNumerator_thermal B hB hJ hcut j ht).indicator measurableSet_Ioi

/-- The full repair has no atom at the cutoff, since every actual cell node
lies strictly below it. -/
theorem repairOutput_cutoff_singleton (j : ℤ) {t : ℝ} (ht : 0 < t) :
    cell.repairOutput B hB hJ hcut j t {B} = 0 := by
  have hn : ∀ i : Fin cell.count, cell.node i ≠ B :=
    fun i => ne_of_lt ((cell.node_mem i).2.trans_lt hcut)
  simp [cell.repairOutput_singleton B hB hJ hcut j ht B, hn]

/-- On the exterior, the complete repair is its actual ordinary kernel density. -/
theorem repairOutput_restrict_exterior (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (cell.repairOutput B hB hJ hcut j t).restrict (Ioi B) =
      (referenceMeasure j).withDensityᵥ (fun e => if B < e then
        Real.exp (-t * e) * cell.exteriorNumerator B hB j e else 0) := by
  change (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
    (canonicalLocalRepairInput cell.rowInput B hB _) j t).restrict _ = _
  rw [canonicalLocalRepairOutput_restrict_exterior cell.rowInput B hB
    (cell.rowInput_physicalSupport B hB hJ hcut) (cell.rowInput_inside B hcut) j ht]
  exact restricted_density_eq_indicator (referenceMeasure j) (Ioi B) measurableSet_Ioi _
    (cell.integrable_exteriorNumerator_thermal B hB hJ hcut j ht).restrict

/-- The complete actual output is the single-row thermal cell residual plus
its exterior density. The lower, upper, and cutoff pieces exhaust the real line. -/
theorem repairOutput_eq_residual_add_exterior (j : ℤ) {t : ℝ} (ht : 0 < t) :
    cell.repairOutput B hB hJ hcut j t =
      (if j = J then thermalSignedInputMeasure cell.residual t else 0) +
        (referenceMeasure j).withDensityᵥ (fun e => if B < e then
          Real.exp (-t * e) * cell.exteriorNumerator B hB j e else 0) := by
  rw [signedMeasure_cutoff_partition _ B
    (cell.repairOutput_cutoff_singleton B hB hJ hcut j ht),
    cell.repairOutput_below_cutoff B hB hJ hcut j ht,
    cell.repairOutput_restrict_exterior B hB hJ hcut j ht]

end InitialReferenceCell
end GapFamily.Construction
