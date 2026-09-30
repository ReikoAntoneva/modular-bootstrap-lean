import GapFamily.Construction.TailCellStateUpdate
import GapFamily.Construction.LayerScheduleBlock

/-! Cutoff geometry for literal finite repair states.  A live cell starts below
the next integer frontier, so its endpoint is below the following integer.
The resulting upper-front bound supplies the hypothesis of the actual
pointwise clearing theorem. -/

noncomputable section
namespace GapFamily.Construction
open Set MeasureTheory Analytic

theorem one_le_layerCutoff {U : ℝ} (hU : 0 ≤ U) (m : ℕ) :
    1 ≤ layerCutoff U m := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  dsimp [layerCutoff]
  linarith

/-- Both the original endpoint bound and the current layer endpoint bound
lie strictly below the common repair cutoff. -/
theorem max_initial_layer_lt_layerCutoff {U : ℝ} (hU : 0 ≤ U) (m : ℕ) :
    max (U + 1) ((m : ℝ) + 2) < layerCutoff U m := by
  apply max_lt_iff.mpr
  constructor
  · exact lt_layerCutoff_of_initial_upper le_rfl
  · have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    dsimp [layerCutoff]
    linarith

namespace TailCell

/-- The actual selected endpoint fits the layer cutoff using only the live
slot guard and the proved endpoint range of the selected cell. -/
theorem right_lt_layerCutoff {J : ℤ} {L U : ℝ} {k m : ℕ} {q : ℝ → ℝ}
    (cell : TailCell J L k q) (hU : 0 ≤ U) (hactive : L < (m : ℝ) + 1) :
    cell.right < layerCutoff U m := by
  apply lt_layerCutoff_of_layer_upper hU
  linarith [cell.right_mem.2]

end TailCell

namespace FiniteRepairState

variable (s : FiniteRepairState)

/-- The upper-front bound during a layer contains the whole cleared physical
region in the same cutoff used by its actual modular repairs. -/
theorem front_le_layerCutoff_of_layer_upper {U : ℝ} {m : ℕ} (hU : 0 ≤ U)
    (hf : ∀ j : ℤ, s.front j ≤ max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|)) :
    ∀ j : ℤ, s.front j ≤ max (layerCutoff U m) |(j : ℝ)| := by
  intro j
  apply (hf j).trans
  rw [← max_assoc]
  exact max_le_max_right _ (max_initial_layer_lt_layerCutoff hU m).le

/-- Every physical energy strictly below an actual row front is strictly
below the common cutoff. -/
theorem cleared_energy_lt_layerCutoff {U : ℝ} {m : ℕ} (hU : 0 ≤ U)
    (hf : ∀ j : ℤ, s.front j ≤ max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|))
    (j : ℤ) (E : ℝ) (hphysical : |(j : ℝ)| ≤ E) (hE : E < s.front j) :
    E < layerCutoff U m := by
  have h := hE.trans_le (s.front_le_layerCutoff_of_layer_upper hU hf j)
  rcases lt_max_iff.mp h with h | h
  · exact h
  · exact False.elim ((not_lt_of_ge hphysical) h)

/-- A beginning-of-layer upper bound also satisfies the bound valid at every
intermediate slot in that same layer. -/
theorem layer_start_front_upper {U : ℝ} {m : ℕ}
    (hf : ∀ j : ℤ, s.front j ≤ max (U + 1) (max ((m : ℝ) + 1) |(j : ℝ)|)) :
    ∀ j : ℤ, s.front j ≤ max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|) := by
  intro j
  exact (hf j).trans (max_le_max_left _ (max_le_max_right _ (by linarith)))

/-- The completed layer bound is exactly the next layer's starting bound. -/
theorem layer_front_upper_succ {U : ℝ} {m : ℕ}
    (hf : ∀ j : ℤ, s.front j ≤ max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|)) :
    ∀ j : ℤ, s.front j ≤ max (U + 1) (max (((m + 1 : ℕ) : ℝ) + 1) |(j : ℝ)|) := by
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hf

variable {J : ℤ} {k : ℕ}
  (cell : TailCell J (s.front J) k (s.numerator J))
  (B : ℝ) (hB : 1 ≤ B) (hJ : |(J : ℝ)| ≤ s.front J) (hcut : cell.right < B)

/-- A literal live-cell update preserves the current layer upper-front bound. -/
theorem addTailCell_layer_front_upper {U : ℝ} {m : ℕ}
    (hf : ∀ j : ℤ, s.front j ≤ max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|))
    (hactive : s.front J < (m : ℝ) + 1) :
    ∀ j : ℤ, (s.addTailCell cell B hB hJ hcut).front j ≤
      max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|) := by
  intro j
  by_cases hj : j = J
  · subst j
    rw [addTailCell_front_same]
    have hr : cell.right ≤ (m : ℝ) + 2 := by linarith [cell.right_mem.2]
    exact hr.trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [addTailCell_front_other _ _ _ _ _ _ hj]
    exact hf j

include hJ in
/-- The new unit-node occurrences obey the exact layer interval and physical
spin bounds used by the finite schedule. -/
theorem addTailCell_new_node_layer_bounds {m : ℕ}
    (hlower : (m : ℝ) ≤ s.front J) (hactive : s.front J < (m : ℝ) + 1)
    (p : ℝ × ℤ) (hp : p ∈ List.ofFn (fun i => (cell.node i, J))) :
    (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2 ∧ |(p.2 : ℝ)| ≤ p.1 := by
  obtain ⟨hlo, hhi, hspin⟩ := s.addTailCell_node_bounds cell p hp
  refine ⟨hlower.trans hlo, ?_, ?_⟩
  · linarith [cell.right_mem.2]
  · rw [hspin]
    exact hJ.trans hlo

/-- All old and new node occurrences stay below the same cutoff. -/
theorem addTailCell_nodes_lt_cutoff
    (hnodes : ∀ p ∈ s.nodes, p.1 < B) :
    ∀ p ∈ (s.addTailCell cell B hB hJ hcut).nodes, p.1 < B := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hnodes p hp
  · exact (s.addTailCell_node_bounds cell p hp).2.1.trans_lt hcut

/-- The actual unit atoms keep their physical spin-energy relation. -/
theorem addTailCell_nodes_physical
    (hnodes : ∀ p ∈ s.nodes, |(p.2 : ℝ)| ≤ p.1) :
    ∀ p ∈ (s.addTailCell cell B hB hJ hcut).nodes, |(p.2 : ℝ)| ≤ p.1 := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hnodes p hp
  · obtain ⟨hlo, _, hspin⟩ := s.addTailCell_node_bounds cell p hp
    rw [hspin]
    exact hJ.trans hlo

/-- The actual clearing theorem applies at the explicit layer cutoff; its
front premise is discharged by the concrete layer geometry. -/
theorem addTailCell_cleared_layerCutoff {U : ℝ} {m : ℕ} (hU : 0 ≤ U)
    (hactive : s.front J < (m : ℝ) + 1) (hc : s.Cleared)
    (hf : ∀ j : ℤ, s.front j ≤ max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|)) :
    (s.addTailCell cell (layerCutoff U m) (one_le_layerCutoff hU m) hJ
      (cell.right_lt_layerCutoff hU hactive)).Cleared := by
  exact s.addTailCell_cleared cell _ _ hJ _ hc
    (s.front_le_layerCutoff_of_layer_upper hU hf)

end FiniteRepairState
end GapFamily.Construction
