import GapFamily.Construction.FiniteRepairState
import GapFamily.Construction.CellThermalUpdate
import GapFamily.Construction.TailCellRepairDatum

/-! One actual C9 state update. The cell is typed by the current front and
current continuum. Exactly its canonical modular repair is appended to the
history, its unit atoms are appended to the atom list, and its ordinary
continuum is replaced using the proved full exterior output. -/

noncomputable section
namespace GapFamily.Construction
open Set MeasureTheory Analytic

namespace FiniteRepairState

variable (s : FiniteRepairState) {J : ℤ} {k : ℕ}
  (cell : TailCell J (s.front J) k (s.numerator J))
  (B : ℝ) (hB : 1 ≤ B) (hJ : |(J : ℝ)| ≤ s.front J) (hcut : cell.right < B)

/-- The literal finite update uses the same actual cell in all four data fields. -/
def addTailCell : FiniteRepairState where
  front := cellFrontUpdate s.front J cell.right
  nodes := s.nodes ++ List.ofFn (fun i => (cell.node i, J))
  numerator := cellNumeratorUpdate s.numerator (cell.exteriorNumerator B hB)
    J (s.front J) cell.right B
  history := s.history ++ [cell.repairDatum B hB hJ hcut]

@[simp] theorem addTailCell_front_same :
    (s.addTailCell cell B hB hJ hcut).front J = cell.right := by
  exact cellFrontUpdate_same s.front J cell.right

theorem addTailCell_front_other {j : ℤ} (hj : j ≠ J) :
    (s.addTailCell cell B hB hJ hcut).front j = s.front j :=
  cellFrontUpdate_other s.front J cell.right hj

theorem addTailCell_front_advance :
    s.front J + 1 / 2 ≤ (s.addTailCell cell B hB hJ hcut).front J := by
  rw [addTailCell_front_same]
  exact cell.right_mem.1

theorem addTailCell_front_upper :
    (s.addTailCell cell B hB hJ hcut).front J ≤ s.front J + 1 := by
  rw [addTailCell_front_same]
  exact cell.right_mem.2

theorem addTailCell_front_mono (j : ℤ) :
    s.front j ≤ (s.addTailCell cell B hB hJ hcut).front j :=
  cellFrontUpdate_mono s.front J cell.right (by linarith [cell.right_mem.1]) j

theorem addTailCell_frontInvariant {m : ℕ} (hf : FrontInvariant m FiniteRepairState.front s) :
    FrontInvariant m FiniteRepairState.front (s.addTailCell cell B hB hJ hcut) := by
  intro j
  exact (hf j).trans (s.addTailCell_front_mono cell B hB hJ hcut j)

/-- All previously constructed node occurrences remain literally present. -/
theorem addTailCell_nodes_prefix : s.nodes.IsPrefix (s.addTailCell cell B hB hJ hcut).nodes :=
  ⟨List.ofFn (fun i => (cell.node i, J)), rfl⟩

theorem addTailCell_node_bounds (p : ℝ × ℤ)
    (hp : p ∈ List.ofFn (fun i => (cell.node i, J))) :
    s.front J ≤ p.1 ∧ p.1 ≤ cell.right ∧ p.2 = J := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨(cell.node_mem i).1, (cell.node_mem i).2, rfl⟩

/-- The new nodes are exactly the cell's actual unit atoms in the thermal output. -/
theorem addTailCell_atomicThermalOutput (b : ℝ) (j : ℤ) (t : ℝ) :
    (s.addTailCell cell B hB hJ hcut).atomicThermalOutput b j t =
      s.atomicThermalOutput b j t +
        (if j = J then thermalSignedInputMeasure (unitAtomSignedMeasure cell.node) t else 0) := by
  change unitMarkerThermalMeasure b j t +
    unitNodeRowThermalMeasure (s.nodes ++ List.ofFn (fun i => (cell.node i, J))) j t = _
  rw [unitNodeRowThermalMeasure_append, unitNodeRowThermalMeasure_ofFn,
    thermalSignedInputMeasure_unitAtomSignedMeasure]
  simp only [atomicThermalOutput]
  abel

/-- The complete ordinary continuum remains thermally integrable after the
actual canonical repair; the exterior part has already been proved integrable. -/
theorem addTailCell_thermalIntegrable (hq : s.ThermalIntegrable) :
    (s.addTailCell cell B hB hJ hcut).ThermalIntegrable := by
  intro j t ht
  exact cell.integrable_thermal_numeratorUpdate B hB hJ hcut j ht (hq j t ht)

/-- The common cutoff continues to contain the entire cleared physical region. -/
theorem addTailCell_front_le_cutoff
    (hf : ∀ j : ℤ, s.front j ≤ max B |(j : ℝ)|) :
    ∀ j : ℤ, (s.addTailCell cell B hB hJ hcut).front j ≤ max B |(j : ℝ)| := by
  intro j
  by_cases hj : j = J
  · subst j
    rw [addTailCell_front_same]
    exact hcut.le.trans (le_max_left _ _)
  · rw [addTailCell_front_other _ _ _ _ _ _ hj]
    exact hf j

/-- Pointwise continuum clearing is preserved by the actual update because
the complete exterior correction starts beyond the common repair cutoff. -/
theorem addTailCell_cleared (hc : s.Cleared)
    (hf : ∀ j : ℤ, s.front j ≤ max B |(j : ℝ)|) :
    (s.addTailCell cell B hB hJ hcut).Cleared := by
  intro j E hphysical hE
  exact cellNumeratorUpdate_cleared s.numerator (cell.exteriorNumerator B hB)
    s.front J (s.front J) cell.right B rfl hcut.le hf hc j E hphysical hE

/-- Every still-unprocessed point sees only the actual exterior numerator;
the direct cell replacement never subtracts its newly selected endpoint. -/
theorem addTailCell_numerator_unprocessed (j : ℤ) (E : ℝ)
    (hE : (s.addTailCell cell B hB hJ hcut).front j ≤ E) :
    (s.addTailCell cell B hB hJ hcut).numerator j E =
      s.numerator j E + if B < E then cell.exteriorNumerator B hB j E else 0 :=
  cellNumeratorUpdate_unprocessed s.numerator (cell.exteriorNumerator B hB)
    s.front J (s.front J) cell.right B j E hE

/-- The actual one-cell exterior estimate supplies the exact local error
contract used by the already constructed finite schedule. -/
theorem addTailCell_error (ε : ℝ) (H : ℝ → ℝ) (hε : 0 ≤ ε) (hH : ∀ E, 0 ≤ H E)
    (herror : ∀ (j : ℤ) (E : ℝ), |(j : ℝ)| ≤ E → B < E →
      |cell.exteriorNumerator B hB j E| ≤ ε * H E)
    (j : ℤ) (E : ℝ) (hphysical : |(j : ℝ)| ≤ E)
    (hE : (s.addTailCell cell B hB hJ hcut).front j ≤ E) :
    |(s.addTailCell cell B hB hJ hcut).numerator j E - s.numerator j E| ≤ ε * H E :=
  cellNumeratorUpdate_error s.numerator (cell.exteriorNumerator B hB)
    s.front J (s.front J) cell.right B ε H hε hH herror j E hphysical hE

end FiniteRepairState
end GapFamily.Construction
