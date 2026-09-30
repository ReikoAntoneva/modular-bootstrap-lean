import GapFamily.Construction.CellThermalReplacement
import GapFamily.Construction.CellNumeratorUpdate
import GapFamily.Construction.TailCellRepairDensity

/-!
# Ordinary thermal output of the actual cell update

The finite cell is removed only from its selected row. Its canonical modular
repair adds exactly the new unit atoms and the complete exterior numerator.
Both parts of the updated continuum are ordinarily thermally integrable.
-/

noncomputable section
namespace GapFamily.Construction

open Set MeasureTheory Analytic
open scoped BigOperators Classical

/-- The selected-row clearing convention is exactly the half-open cell removal. -/
theorem clearCellNumerator_self_eq_removeCellDensity (q : ℤ → ℝ → ℝ)
    (J : ℤ) (L V : ℝ) : clearCellNumerator q J L V J = removeCellDensity L V (q J) := by
  funext E
  by_cases hE : E ∈ Ico L V <;> simp [clearCellNumerator, removeCellDensity, hE]

/-- Other rows retain their old continuum before the exterior correction is added. -/
theorem clearCellNumerator_other_eq (q : ℤ → ℝ → ℝ) (J : ℤ) (L V : ℝ)
    {j : ℤ} (hj : j ≠ J) : clearCellNumerator q J L V j = q j := by
  funext E
  simp [clearCellNumerator, hj]

/-- Clearing one row preserves genuine ordinary thermal integrability. -/
theorem integrable_thermal_clearCellNumerator (q : ℤ → ℝ → ℝ)
    (J : ℤ) (L V t : ℝ) (j : ℤ)
    (hq : Integrable (fun E => Real.exp (-t * E) * q j E) (referenceMeasure j)) :
    Integrable (fun E => Real.exp (-t * E) * clearCellNumerator q J L V j E)
      (referenceMeasure j) := by
  by_cases hj : j = J
  · subst j
    rw [clearCellNumerator_self_eq_removeCellDensity]
    exact integrable_thermal_removeCellDensity J L V t hq
  · rw [clearCellNumerator_other_eq q J L V hj]
    exact hq

/-- The literal update's thermal density is the sum of its cleared density
and its actual cutoff-supported exterior density. -/
theorem thermal_cellNumeratorUpdate_eq (q exterior : ℤ → ℝ → ℝ)
    (J : ℤ) (L V B t : ℝ) (j : ℤ) :
    (fun E => Real.exp (-t * E) * cellNumeratorUpdate q exterior J L V B j E) =
      (fun E => Real.exp (-t * E) * clearCellNumerator q J L V j E) +
        (fun E => if B < E then Real.exp (-t * E) * exterior j E else 0) := by
  funext E
  by_cases hE : B < E <;> simp [cellNumeratorUpdate, hE, mul_add]

theorem integrable_thermal_cellNumeratorUpdate (q exterior : ℤ → ℝ → ℝ)
    (J : ℤ) (L V B t : ℝ) (j : ℤ)
    (hq : Integrable (fun E => Real.exp (-t * E) * q j E) (referenceMeasure j))
    (hexterior : Integrable (fun E => if B < E then Real.exp (-t * E) * exterior j E else 0)
      (referenceMeasure j)) :
    Integrable (fun E => Real.exp (-t * E) * cellNumeratorUpdate q exterior J L V B j E)
      (referenceMeasure j) := by
  rw [thermal_cellNumeratorUpdate_eq]
  exact (integrable_thermal_clearCellNumerator q J L V t j hq).add hexterior

/-- Exact ordinary signed-measure addition for the literal new numerator. -/
theorem thermalDensity_cellNumeratorUpdate (q exterior : ℤ → ℝ → ℝ)
    (J : ℤ) (L V B t : ℝ) (j : ℤ)
    (hq : Integrable (fun E => Real.exp (-t * E) * q j E) (referenceMeasure j))
    (hexterior : Integrable (fun E => if B < E then Real.exp (-t * E) * exterior j E else 0)
      (referenceMeasure j)) :
    (referenceMeasure j).withDensityᵥ
        (fun E => Real.exp (-t * E) * cellNumeratorUpdate q exterior J L V B j E) =
      (referenceMeasure j).withDensityᵥ
        (fun E => Real.exp (-t * E) * clearCellNumerator q J L V j E) +
      (referenceMeasure j).withDensityᵥ
        (fun E => if B < E then Real.exp (-t * E) * exterior j E else 0) := by
  rw [thermal_cellNumeratorUpdate_eq,
    withDensityᵥ_add (integrable_thermal_clearCellNumerator q J L V t j hq) hexterior]

namespace TailCell

variable {J : ℤ} {L : ℝ} {k : ℕ} {q : ℤ → ℝ → ℝ}
  (cell : TailCell J L k (q J)) (B : ℝ) (hB : 1 ≤ B)
  (hJ : |(J : ℝ)| ≤ L) (hcut : cell.right < B)
include hJ hcut

/-- The canonical exterior theorem proves integrability of the actual updated
continuum, without an integrability premise about that final density. -/
theorem integrable_thermal_numeratorUpdate (j : ℤ) {t : ℝ} (ht : 0 < t)
    (hq : Integrable (fun E => Real.exp (-t * E) * q j E) (referenceMeasure j)) :
    Integrable (fun E => Real.exp (-t * E) *
      cellNumeratorUpdate q (cell.exteriorNumerator B hB) J L cell.right B j E)
      (referenceMeasure j) := by
  exact integrable_thermal_cellNumeratorUpdate q (cell.exteriorNumerator B hB)
    J L cell.right B t j hq
    (cell.integrable_exteriorNumerator_indicator_thermal B hB hJ hcut j ht)

/-- The actual canonical cell repair transforms the old row continuum into the
new unit atoms plus the literal updated continuum, as ordinary signed measures. -/
theorem thermalReplacement (j : ℤ) {t : ℝ} (ht : 0 < t)
    (hq : Integrable (fun E => Real.exp (-t * E) * q j E) (referenceMeasure j)) :
    (referenceMeasure j).withDensityᵥ (fun E => Real.exp (-t * E) * q j E) +
        cell.repairOutput B hB hJ hcut j t =
      (if j = J then thermalSignedInputMeasure (unitAtomSignedMeasure cell.node) t else 0) +
        (referenceMeasure j).withDensityᵥ (fun E => Real.exp (-t * E) *
          cellNumeratorUpdate q (cell.exteriorNumerator B hB) J L cell.right B j E) := by
  rw [cell.repairOutput_eq_residual_add_exterior B hB hJ hcut j ht,
    thermalDensity_cellNumeratorUpdate q (cell.exteriorNumerator B hB)
      J L cell.right B t j hq
      (cell.integrable_exteriorNumerator_indicator_thermal B hB hJ hcut j ht)]
  by_cases hj : j = J
  · subst j
    rw [ite_eq_left rfl, ite_eq_left rfl, clearCellNumerator_self_eq_removeCellDensity,
      TailCell.residual, thermalSignedInputMeasure_cellResidualMeasure J L cell.right t
        cell.node cell.density_integrable,
      thermal_removeCellDensity_withDensity J L cell.right t hq]
    abel
  · rw [ite_eq_right hj, ite_eq_right hj, clearCellNumerator_other_eq q J L cell.right hj]
    simp only [zero_add]

/-- Previously constructed atoms are retained during the actual modular repair. -/
theorem thermalReplacement_preserves_old (old : SignedMeasure ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t)
    (hq : Integrable (fun E => Real.exp (-t * E) * q j E) (referenceMeasure j)) :
    (old + (referenceMeasure j).withDensityᵥ (fun E => Real.exp (-t * E) * q j E)) +
        cell.repairOutput B hB hJ hcut j t =
      (old + if j = J then thermalSignedInputMeasure (unitAtomSignedMeasure cell.node) t else 0) +
        (referenceMeasure j).withDensityᵥ (fun E => Real.exp (-t * E) *
          cellNumeratorUpdate q (cell.exteriorNumerator B hB) J L cell.right B j E) := by
  rw [add_assoc, cell.thermalReplacement B hB hJ hcut j ht hq, ← add_assoc]

end TailCell
end GapFamily.Construction
