import GapFamily.Layer

/-! Exact finite layer budgets and quantitative control of every remaining tail. -/

namespace GapFamily.Construction

/-- Every finite block of layers has the exact telescoping budget. -/
theorem sum_layerBudget_add (m N : ℕ) :
    (∑ n ∈ Finset.range N, Layer.layerBudget (m + n)) =
      (1 / 256 : ℝ) * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + N + 1)) := by
  have h := Finset.sum_range_add Layer.layerBudget m N
  rw [Layer.sum_layerBudget, Layer.sum_layerBudget] at h
  simp only [Nat.cast_add] at h
  linarith

/-- Dropping finitely many layers preserves ordinary summability. -/
theorem summable_layerBudget_add (m : ℕ) :
    Summable (fun n : ℕ => Layer.layerBudget (m + n)) := by
  simpa only [Nat.add_comm] using (summable_nat_add_iff m).mpr Layer.summable_layerBudget

/-- The error still available after the first `m` layers decays as `1 / (m + 1)`. -/
theorem tsum_layerBudget_add_le (m : ℕ) :
    (∑' n : ℕ, Layer.layerBudget (m + n)) ≤ (1 / 256 : ℝ) / ((m : ℝ) + 1) := by
  have hsplit :
      (∑ n ∈ Finset.range m, Layer.layerBudget n) +
        (∑' n : ℕ, Layer.layerBudget (m + n)) = ∑' n : ℕ, Layer.layerBudget n := by
    simpa only [Nat.add_comm] using Layer.summable_layerBudget.sum_add_tsum_nat_add m
  rw [Layer.sum_layerBudget] at hsplit
  calc
    (∑' n : ℕ, Layer.layerBudget (m + n)) =
        (∑' n : ℕ, Layer.layerBudget n) -
          (1 / 256 : ℝ) * (1 - 1 / ((m : ℝ) + 1)) := by linarith
    _ ≤ (1 / 256 : ℝ) - (1 / 256 : ℝ) * (1 - 1 / ((m : ℝ) + 1)) :=
      sub_le_sub_right Layer.tsum_layerBudget_le _
    _ = (1 / 256 : ℝ) / ((m : ℝ) + 1) := by ring

end GapFamily.Construction
