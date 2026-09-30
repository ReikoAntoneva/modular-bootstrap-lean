import BTZEntropy.Comparison.SpectrumTestPrefix
import GapFamily.Construction.RealTailCellThermal

/-! Exact decomposition of compact spectral tests into actual repair cells.
The cell at each slot is the one selected at its literal preceding state. -/

noncomputable section
open GapFamily GapFamily.Construction
open scoped Classical

namespace BTZEntropy.Comparison

variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
  (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)

/-- The test of an actual cell emission, zero at every inactive slot. -/
def scheduledCellTest (f : ℝ × ℤ → ℝ) (p : LayerSlotIndex T) : ℝ :=
  if h : RealTailStepValid a T (d.slotPreState initial p) p.layer p.row then
    ∑ i : Fin (d.cell _ _ _ h).count, f ((d.cell _ _ _ h).node i, p.row)
  else 0

/-- The finite cell test equals the actual emitted list, with all repeated
occurrences retained and with exactly the scheduler's inactive convention. -/
theorem scheduledCellTest_eq_list (f : ℝ × ℤ → ℝ) (p : LayerSlotIndex T) :
    scheduledCellTest d initial f p =
      ((scheduledSlotNodeList T FiniteRepairState.front d.step d.nodeList initial p).map f).sum := by
  rw [d.scheduledSlotNodeList_eq_raw]
  unfold scheduledCellTest RealTailLocalData.nodeList
  split_ifs with h
  · simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  · rfl

/-- On an active slot the test is exactly the node sum of the same `TailCell`
to which the proved moment and variation estimates apply. -/
theorem scheduledCellTest_active (f : ℝ × ℤ → ℝ) (p : d.ActiveSlot initial) :
    scheduledCellTest d initial f p.val =
      ∑ i : Fin (d.activeCell initial p).count,
        f ((d.activeCell initial p).node i, p.val.row) := by
  rw [scheduledCellTest, dite_eq_left p.property]
  rfl

/-- A complete finite layer is precisely the finite sum of its chronological
actual cell tests, not a family of independently selected quadratures. -/
theorem layerNodeTest_eq_cellTest (f : ℝ × ℤ → ℝ) (m : ℕ) :
    ((scheduledLayerBlock T FiniteRepairState.front d.step d.nodeList initial m).map f).sum =
      ∑ q : Fin (layerSlots (T + m)).length, scheduledCellTest d initial f ⟨m, q⟩ := by
  rw [scheduledLayerBlock_eq_flatten_ofFn, sum_flatten_ofFn]
  apply Finset.sum_congr rfl
  intro q _
  exact (scheduledCellTest_eq_list d initial f ⟨m, q⟩).symm

/-- The finite evolving state contains the initial packet and the tests of
all actual cells in its completed layers. -/
theorem stateNodeTest_eq_initial_add_cell (f : ℝ × ℤ → ℝ) (k : ℕ) :
    (((d.state initial k).nodes).map f).sum = (initial.nodes.map f).sum +
      ∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
        scheduledCellTest d initial f ⟨m, q⟩ := by
  rw [stateNodeTest_eq_initial_add_layer]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  exact layerNodeTest_eq_cellTest d initial f m

/-- Compact permanent-spectrum tests split exactly into the original marker,
initial packet, and genuine tail cells from a finite construction prefix. -/
theorem realPermanentNodeTest_eq_initial_add_cell
    (b : ℝ) (hb : 0 ≤ b) (hbT : b ≤ (T : ℝ))
    (hinitial : ∀ p ∈ initial.nodes, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (f : ℝ × ℤ → ℝ) (B : ℝ) (hf : ∀ p, B ≤ p.1 → f p = 0)
    (k : ℕ) (hBk : B ≤ ((T + k : ℕ) : ℝ)) :
    (∑' i : (d.permanentSpectrumData b hb hbT initial hinitial).Node,
      f ((d.permanentSpectrumData b hb hbT initial hinitial).energy i,
        (d.permanentSpectrumData b hb hbT initial hinitial).spin i)) =
      f (b, 0) + (initial.nodes.map f).sum +
        ∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
          scheduledCellTest d initial f ⟨m, q⟩ := by
  rw [realPermanentNodeTest_eq_state d initial b hb hbT hinitial f B hf k hBk,
    stateNodeTest_eq_initial_add_cell, add_assoc]

end BTZEntropy.Comparison
