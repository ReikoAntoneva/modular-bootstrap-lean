import GapFamily.Construction.CellCoordinateGeometry

/-!
# Returning the prescribed unit nodes to physical energy

The index type remains exactly `Fin N`; only each node's coordinate changes.
The matched tests in energy are polynomials in `sqrt(E-r)`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace GapFamily.Construction

/-- Return the same prescribed tuple of unit nodes to the physical energy coordinate. -/
def physicalCellNode {N : ℕ} (r : ℝ) (node : Fin N → ℝ) : Fin N → ℝ :=
  fun i => energyCoord r (node i)

theorem physicalCellNode_mem {N : ℕ} {r L V : ℝ} (hL : r ≤ L) (hV : r ≤ V)
    (node : Fin N → ℝ)
    (hnode : ∀ i, node i ∈ Icc (rootCoord r L) (rootCoord r V)) (i : Fin N) :
    physicalCellNode r node i ∈ Icc L V :=
  energyCoord_mem_Icc r hL hV (hnode i)

/-- Strict root-coordinate nodes remain strictly inside the physical cell. -/
theorem physicalCellNode_mem_Ioo {N : ℕ} {r L V : ℝ} (hL : r ≤ L) (hV : r ≤ V)
    (node : Fin N → ℝ)
    (hnode : ∀ i, node i ∈ Ioo (rootCoord r L) (rootCoord r V)) (i : Fin N) :
    physicalCellNode r node i ∈ Ioo L V := by
  have h := (energyCoord_mem_Ioo_iff r (rootCoord_nonneg r L) (rootCoord_nonneg r V)
    ((rootCoord_nonneg r L).trans (hnode i).1.le)).mpr (hnode i)
  simpa only [physicalCellNode, energyCoord_rootCoord r hL,
    energyCoord_rootCoord r hV] using h

/-- Every coordinate test has exactly the same unit sum after inverse transport. -/
theorem physicalCellNode_test_sum {N : ℕ} {r L V : ℝ}
    (node : Fin N → ℝ)
    (hnode : ∀ i, node i ∈ Icc (rootCoord r L) (rootCoord r V)) (φ : ℝ → ℝ) :
    (∑ i, φ (rootCoord r (physicalCellNode r node i))) = ∑ i, φ (node i) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [physicalCellNode, rootCoord_energyCoord r
    ((rootCoord_nonneg r L).trans (hnode i).1)]

end GapFamily.Construction
