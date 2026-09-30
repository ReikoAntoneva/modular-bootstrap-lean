import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Absolute coefficient sum

The finite sum of absolute values of polynomial coefficients supplies explicit
constants for estimates on the unit interval and on Taylor remainders.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace BTZEntropy

/-- The sum of the absolute values of all coefficients. -/
def polynomialCoeffNorm (p : Polynomial ℝ) : ℝ :=
  p.sum (fun _ a => |a|)

theorem polynomialCoeffNorm_nonneg (p : Polynomial ℝ) :
    0 ≤ polynomialCoeffNorm p := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

@[simp] theorem polynomialCoeffNorm_zero :
    polynomialCoeffNorm 0 = 0 := by
  simp [polynomialCoeffNorm]

@[simp] theorem polynomialCoeffNorm_monomial (n : ℕ) (a : ℝ) :
    polynomialCoeffNorm (monomial n a) = |a| := by
  simp [polynomialCoeffNorm]

@[simp] theorem polynomialCoeffNorm_C (a : ℝ) :
    polynomialCoeffNorm (C a) = |a| := by
  simp [polynomialCoeffNorm]

@[simp] theorem polynomialCoeffNorm_one :
    polynomialCoeffNorm 1 = 1 := by
  simpa using polynomialCoeffNorm_C 1

theorem polynomialCoeffNorm_add_le (p q : Polynomial ℝ) :
    polynomialCoeffNorm (p + q) ≤ polynomialCoeffNorm p + polynomialCoeffNorm q := by
  unfold polynomialCoeffNorm
  rw [Polynomial.sum_eq_of_subset (fun (_ : ℕ) (a : ℝ) => |a|) (by simp)
    Polynomial.support_add]
  rw [Polynomial.sum_eq_of_subset (fun (_ : ℕ) (a : ℝ) => |a|) (by simp)
    (Finset.subset_union_left : p.support ⊆ p.support ∪ q.support)]
  rw [Polynomial.sum_eq_of_subset (fun (_ : ℕ) (a : ℝ) => |a|) (by simp)
    (Finset.subset_union_right : q.support ⊆ p.support ∪ q.support)]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun n _ => by simpa using abs_add_le (p.coeff n) (q.coeff n))

@[simp] theorem polynomialCoeffNorm_neg (p : Polynomial ℝ) :
    polynomialCoeffNorm (-p) = polynomialCoeffNorm p := by
  simp [polynomialCoeffNorm, Polynomial.sum]

theorem polynomialCoeffNorm_sub_le (p q : Polynomial ℝ) :
    polynomialCoeffNorm (p - q) ≤ polynomialCoeffNorm p + polynomialCoeffNorm q := by
  simpa only [sub_eq_add_neg, polynomialCoeffNorm_neg] using polynomialCoeffNorm_add_le p (-q)

theorem polynomialCoeffNorm_sum_le {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial ℝ) :
    polynomialCoeffNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polynomialCoeffNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (polynomialCoeffNorm_add_le _ _).trans (add_le_add le_rfl ih)

theorem abs_coeff_le_polynomialCoeffNorm (p : Polynomial ℝ) (n : ℕ) :
    |p.coeff n| ≤ polynomialCoeffNorm p := by
  by_cases hn : n ∈ p.support
  · exact Finset.single_le_sum (f := fun k => |p.coeff k|)
      (fun _ _ => abs_nonneg _) hn
  · simp only [Polynomial.mem_support_iff, not_not] at hn
    simpa only [hn, abs_zero] using polynomialCoeffNorm_nonneg p

theorem abs_eval_le_polynomialCoeffNorm (p : Polynomial ℝ) (ε : ℝ)
    (hε : |ε| ≤ 1) : |p.eval ε| ≤ polynomialCoeffNorm p := by
  rw [Polynomial.eval_eq_sum]
  unfold polynomialCoeffNorm Polynomial.sum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro n hn
  rw [abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg ε) hε)

end BTZEntropy
