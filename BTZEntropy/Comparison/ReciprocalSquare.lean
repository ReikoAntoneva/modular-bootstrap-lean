import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# An elementary bound for the reciprocal square series

The bound uses a telescoping majorant, so no evaluation of the Basel sum is
needed in the thermal partition estimate.
-/

namespace BTZEntropy

/-- A finite reciprocal square sum has a uniform telescoping upper bound. -/
theorem sum_range_reciprocal_square_le (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ^ 2) ≤
      2 - 2 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have h1 : 0 < (N : ℝ) + 1 := by positivity
    have h2 : 0 < (N : ℝ) + 2 := by positivity
    have hstep : 1 / ((N : ℝ) + 1) ^ 2 ≤
        2 / ((N : ℝ) + 1) - 2 / ((N : ℝ) + 2) := by
      apply (div_le_iff₀ (sq_pos_of_pos h1)).2
      field_simp
      nlinarith
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]
    norm_num only at *
    linarith

/-- The positive-index reciprocal square series is summable. -/
theorem summable_reciprocal_square :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  apply summable_of_sum_range_le (c := 2) (fun n => by positivity)
  intro N
  exact (sum_range_reciprocal_square_le N).trans
    (sub_le_self _ (by positivity))

/-- A convenient explicit bound for the positive-index reciprocal square series. -/
theorem tsum_reciprocal_square_le_two :
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by
  apply summable_reciprocal_square.tsum_le_of_sum_range_le
  intro N
  exact (sum_range_reciprocal_square_le N).trans
    (sub_le_self _ (by positivity))

end BTZEntropy
