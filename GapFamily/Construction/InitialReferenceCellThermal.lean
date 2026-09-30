import GapFamily.Construction.InitialReferenceCellResidual
import GapFamily.Construction.CellThermalReplacement

/-!
# Atom and thermal identity of an initial reference cell

The ordinary continuum has no atoms. The actual signed residual therefore
retains the literal multiplicity of every selected unit node. Thermal
weighting replaces the continuum on the cell by those same nodes, with
ordinary integrability supplied by the compact cell.
-/

noncomputable section

open Set MeasureTheory
open GapFamily.Analytic
open scoped BigOperators Classical

namespace GapFamily.Construction

/-- Coincident nodes retain their literal unit multiplicity; the ordinary
continuum contributes no singleton mass. -/
theorem InitialReferenceCell.residual_singleton
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) (e : ℝ) :
    cell.residual {e} = ∑ i : Fin cell.count, if cell.node i = e then (1 : ℝ) else 0 := by
  rw [InitialReferenceCell.residual, cellResidualMeasure_apply j L cell.right cell.node
    cell.density_integrable (measurableSet_singleton e)]
  simp

/-- Every initial-cell residual atom has nonnegative integer mass. -/
theorem InitialReferenceCell.residual_singleton_nonneg
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) (e : ℝ) :
    0 ≤ cell.residual {e} := by
  rw [cell.residual_singleton]
  exact Finset.sum_nonneg (fun _ _ => by split <;> norm_num)

/-- No residual atom lies outside the actual closed node interval. -/
theorem InitialReferenceCell.residual_singleton_eq_zero_of_not_mem
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) {e : ℝ} (he : e ∉ Icc L cell.right) :
    cell.residual {e} = 0 := by
  rw [cell.residual_singleton]
  apply Finset.sum_eq_zero
  intro i _
  have hi : cell.node i ≠ e := fun hi => he (hi ▸ cell.node_mem i)
  exact ite_eq_right hi

/-- The initial cell places no atom below its left endpoint. -/
theorem InitialReferenceCell.residual_singleton_eq_zero_of_lt
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) {e : ℝ} (he : e < L) :
    cell.residual {e} = 0 :=
  cell.residual_singleton_eq_zero_of_not_mem (fun hmem => (not_le.mpr he) hmem.1)

/-- The actual cell continuum plus its residual is exactly the finite unit
atom measure. -/
theorem InitialReferenceCell.continuum_add_residual
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) :
    ((referenceMeasure j).restrict (Ioo L cell.right)).withDensityᵥ q +
      cell.residual = unitAtomSignedMeasure cell.node := by
  unfold InitialReferenceCell.residual cellResidualMeasure
  abel

/-- The actual initial-cell residual has an ordinary thermal integral for
every real thermal parameter. -/
theorem InitialReferenceCell.residual_thermal_integrable
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) (t : ℝ) :
    cell.residual.Integrable (fun E => Real.exp (-t * E)) :=
  cellResidualMeasure_thermal_integrable j L cell.right t cell.node cell.density_integrable

/-- Thermal weighting preserves the exact replacement of the ordinary cell
continuum by the finite node measure. Compactness suffices for every real `t`. -/
theorem InitialReferenceCell.continuum_add_residual_thermal
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) (t : ℝ) :
    thermalSignedInputMeasure
        (((referenceMeasure j).restrict (Ioo L cell.right)).withDensityᵥ q) t +
      thermalSignedInputMeasure cell.residual t =
        thermalSignedInputMeasure (unitAtomSignedMeasure cell.node) t := by
  unfold InitialReferenceCell.residual cellResidualMeasure
  rw [thermalSignedInputMeasure_sub_of_integrable _ _ t
    (unitAtomSignedMeasure_thermal_integrable cell.node t)
    (cellDensity_thermal_integrable j L cell.right t cell.density_integrable).1]
  abel

/-- The density form of the thermal replacement uses the actual ordinary
weighted numerator on the open cell. -/
theorem InitialReferenceCell.thermal_continuum_add_residual
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) (t : ℝ) :
    ((referenceMeasure j).restrict (Ioo L cell.right)).withDensityᵥ
        (fun E => Real.exp (-t * E) * q E) +
      thermalSignedInputMeasure cell.residual t =
        thermalSignedInputMeasure (unitAtomSignedMeasure cell.node) t := by
  rw [InitialReferenceCell.residual,
    thermalSignedInputMeasure_cellResidualMeasure j L cell.right t cell.node
      cell.density_integrable]
  abel

/-- Adding the initial-cell residual to a globally integrable thermal
continuum retains exactly the selected nodes and the continuum outside the
removed cell. -/
theorem InitialReferenceCell.thermal_replacement
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) (t : ℝ)
    (hq : Integrable (fun E => Real.exp (-t * E) * q E) (referenceMeasure j)) :
    (referenceMeasure j).withDensityᵥ (fun E => Real.exp (-t * E) * q E) +
      thermalSignedInputMeasure cell.residual t =
        thermalSignedInputMeasure (unitAtomSignedMeasure cell.node) t +
          (referenceMeasure j).withDensityᵥ
            (fun E => Real.exp (-t * E) * removeCellDensity L cell.right q E) :=
  thermalCellReplacement j L cell.right t cell.node hq

end GapFamily.Construction
