import GapFamily.Construction.TailCellExistence

/-! The actual tail residual retains precisely its prescribed unit atoms. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Classical

namespace GapFamily.Construction

/-- The reference-density part contributes no singleton mass. Coincident unit
nodes retain their literal multiplicity in the signed residual. -/
theorem TailCell.residual_singleton {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (e : ℝ) :
    cell.residual {e} = ∑ i : Fin cell.count, if cell.node i = e then (1 : ℝ) else 0 := by
  rw [TailCell.residual, cellResidualMeasure_apply j L cell.right cell.node
    cell.density_integrable (measurableSet_singleton e)]
  simp

/-- The residual is carried by the actual closed cell in total variation. -/
theorem TailCell.residual_ae_mem {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) :
    ∀ᵐ E ∂cell.residual.variation, E ∈ Icc L cell.right := by
  exact ae_iff.mpr cell.residual_support

/-- Every singleton of the residual has nonnegative integer atomic mass. -/
theorem TailCell.residual_singleton_nonneg {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (e : ℝ) : 0 ≤ cell.residual {e} := by
  rw [cell.residual_singleton]
  exact Finset.sum_nonneg (fun _ _ => by split <;> norm_num)

/-- There are no residual atoms outside the actual closed node interval. -/
theorem TailCell.residual_singleton_eq_zero_of_not_mem
    {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) {e : ℝ} (he : e ∉ Icc L cell.right) :
    cell.residual {e} = 0 := by
  rw [cell.residual_singleton]
  apply Finset.sum_eq_zero
  intro i _
  have hi : cell.node i ≠ e := fun hi => he (hi ▸ cell.node_mem i)
  exact ite_eq_right hi

/-- Later cells never place an atom below their cleared front. -/
theorem TailCell.residual_singleton_eq_zero_of_lt
    {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) {e : ℝ} (he : e < L) : cell.residual {e} = 0 :=
  cell.residual_singleton_eq_zero_of_not_mem (fun hmem => (not_le.mpr he) hmem.1)

end GapFamily.Construction
