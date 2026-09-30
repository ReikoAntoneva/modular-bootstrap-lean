import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# A square-root bound for a truncated inverse-square series

A smooth telescoping majorant avoids choosing an integer cutoff:
`min 1 (t²/(n+1)²) ≤ 4t²/((n+t)(n+t+1))` for `t > 0`.
-/

namespace GapFamily.Analytic

private theorem min_one_sq_div_nat_sq_le_telescope {t : ℝ} (ht : 0 < t) (n : ℕ) :
    min 1 (t ^ 2 / ((n : ℝ) + 1) ^ 2) ≤
      4 * t ^ 2 / ((n : ℝ) + t) - 4 * t ^ 2 / ((n : ℝ) + 1 + t) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha : 0 < (n : ℝ) + t := by positivity
  have hb : 0 < (n : ℝ) + 1 + t := by positivity
  have hk : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  have hd : 0 < ((n : ℝ) + t) * ((n : ℝ) + 1 + t) := mul_pos ha hb
  have heq : 4 * t ^ 2 / ((n : ℝ) + t) - 4 * t ^ 2 / ((n : ℝ) + 1 + t) =
      4 * t ^ 2 / (((n : ℝ) + t) * ((n : ℝ) + 1 + t)) := by
    field_simp
    ring
  rw [heq]
  have hden (u : ℝ) (hu : 0 ≤ u) (hku : (n : ℝ) + 1 + t ≤ 2 * u) :
      ((n : ℝ) + t) * ((n : ℝ) + 1 + t) ≤ 4 * u ^ 2 := by
    calc
      _ ≤ ((n : ℝ) + 1 + t) * ((n : ℝ) + 1 + t) :=
        mul_le_mul_of_nonneg_right (by linarith) hb.le
      _ ≤ (2 * u) * (2 * u) := mul_self_le_mul_self hb.le hku
      _ = 4 * u ^ 2 := by ring
  rcases le_total ((n : ℝ) + 1) t with h | h
  · apply (min_le_left _ _).trans
    apply (le_div_iff₀ hd).2
    simpa only [one_mul] using hden t ht.le (by linarith)
  · apply (min_le_right _ _).trans
    apply (div_le_div_iff₀ hk hd).2
    have hm := mul_le_mul_of_nonneg_left
      (hden ((n : ℝ) + 1) (by positivity) (by linarith)) (sq_nonneg t)
    nlinarith

/-- The finite truncated inverse-square sum has a uniform square-root bound. -/
theorem sum_range_min_one_div_nat_sq_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    ∑ n ∈ Finset.range N, min 1 (x / ((n : ℝ) + 1) ^ 2) ≤ 4 * Real.sqrt x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have ht : 0 < Real.sqrt x := Real.sqrt_pos.2 (lt_of_le_of_ne hx (Ne.symm hx0))
  have hsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        (4 * (Real.sqrt x) ^ 2 / ((n : ℝ) + Real.sqrt x) -
          4 * (Real.sqrt x) ^ 2 / ((n : ℝ) + 1 + Real.sqrt x)) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [hsq] using min_one_sq_div_nat_sq_le_telescope ht n
    _ = 4 * (Real.sqrt x) ^ 2 / Real.sqrt x -
        4 * (Real.sqrt x) ^ 2 / ((N : ℝ) + Real.sqrt x) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] using
        (Finset.sum_range_sub' (fun n : ℕ =>
          4 * (Real.sqrt x) ^ 2 / ((n : ℝ) + Real.sqrt x)) N)
    _ ≤ 4 * (Real.sqrt x) ^ 2 / Real.sqrt x := sub_le_self _ (by positivity)
    _ = 4 * Real.sqrt x := by
      field_simp

/-- Convergence is proved before the totalized `tsum` is used. -/
theorem summable_min_one_div_nat_sq {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => min 1 (x / ((n : ℝ) + 1) ^ 2)) := by
  exact summable_of_sum_range_le (fun n => by positivity)
    (sum_range_min_one_div_nat_sq_le hx)

/-- Summing the smooth majorant yields the explicit constant `4`. -/
theorem tsum_min_one_div_nat_sq_le {x : ℝ} (hx : 0 ≤ x) :
    (∑' n : ℕ, min 1 (x / ((n : ℝ) + 1) ^ 2)) ≤ 4 * Real.sqrt x := by
  exact Real.tsum_le_of_sum_range_le (fun n => by positivity)
    (sum_range_min_one_div_nat_sq_le hx)

/-- An elementary finite bound for the reciprocal-square series. -/
theorem sum_range_one_div_nat_sq_le_two (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by
  have hpoint (n : ℕ) : 1 / ((n : ℝ) + 1) ^ 2 ≤
      2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have ha : 0 < (n : ℝ) + 1 := by positivity
    have hb : 0 < (n : ℝ) + 1 + 1 := by positivity
    have heq : 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) =
        2 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)) := by
      field_simp
      ring
    rw [heq]
    apply (div_le_div_iff₀ (sq_pos_of_pos ha) (mul_pos ha hb)).2
    nlinarith
  calc
    _ ≤ ∑ n ∈ Finset.range N, (2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1)) :=
      Finset.sum_le_sum (fun n _ => hpoint n)
    _ = 2 - 2 / ((N : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, div_one] using
        (Finset.sum_range_sub' (fun n : ℕ => 2 / ((n : ℝ) + 1)) N)
    _ ≤ 2 := sub_le_self _ (by positivity)

/-- Summability of the reciprocal-square majorant. -/
theorem summable_one_div_nat_sq :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) :=
  summable_of_sum_range_le (fun n => by positivity) sum_range_one_div_nat_sq_le_two

/-- The reciprocal-square majorant has sum at most `2`. -/
theorem tsum_one_div_nat_sq_le_two :
    (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) ≤ 2 :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) sum_range_one_div_nat_sq_le_two

end GapFamily.Analytic
