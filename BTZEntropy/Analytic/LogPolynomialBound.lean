import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic

/-!
# Polynomial truncation bound

The error after retaining the powers below `N` is bounded by the coefficient
absolute sum times `|ε| ^ N` on the closed unit interval.  The statement also
covers `N = 0` and the zero polynomial.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace BTZEntropy

theorem polynomial_eval_sub_sum_range_le (p : Polynomial ℝ) (N : ℕ)
    {ε : ℝ} (hε : |ε| ≤ 1) :
    |p.eval ε - ∑ n ∈ Finset.range N, p.coeff n * ε ^ n| ≤
      (p.sum fun _ a => |a|) * |ε| ^ N := by
  have hdegree : p.natDegree < N + (p.natDegree + 1) := by omega
  have heval : p.eval ε - ∑ n ∈ Finset.range N, p.coeff n * ε ^ n =
      ∑ n ∈ Finset.range (p.natDegree + 1), p.coeff (N + n) * ε ^ (N + n) := by
    rw [Polynomial.eval_eq_sum_range' hdegree, Finset.sum_range_add]
    ring
  have hnorm : (∑ n ∈ Finset.range (p.natDegree + 1), |p.coeff (N + n)|) ≤
      p.sum (fun _ a => |a|) := by
    rw [p.sum_over_range' (fun _ => abs_zero) _ hdegree]
    conv_rhs => rw [Finset.sum_range_add]
    exact le_add_of_nonneg_left
      (Finset.sum_nonneg fun n (_ : n ∈ Finset.range N) => abs_nonneg (p.coeff n))
  rw [heval]
  calc
    |∑ n ∈ Finset.range (p.natDegree + 1), p.coeff (N + n) * ε ^ (N + n)|
        ≤ ∑ n ∈ Finset.range (p.natDegree + 1),
          |p.coeff (N + n) * ε ^ (N + n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (p.natDegree + 1), |p.coeff (N + n)| * |ε| ^ N := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (abs_nonneg ε) hε (Nat.le_add_right N n)) (abs_nonneg _)
    _ = (∑ n ∈ Finset.range (p.natDegree + 1), |p.coeff (N + n)|) * |ε| ^ N := by
      rw [Finset.sum_mul]
    _ ≤ (p.sum fun _ a => |a|) * |ε| ^ N :=
      mul_le_mul_of_nonneg_right hnorm (pow_nonneg (abs_nonneg ε) N)

end BTZEntropy
