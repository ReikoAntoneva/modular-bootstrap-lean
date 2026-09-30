import GapFamily.Analytic.Foundation.Vacuum
import GapFamily.Analytic.Foundation.NegativeSeedBound
import GapFamily.Analytic.Foundation.MinSeries

/-!
# The higher-order vacuum remainder

Subtracting the actual denominator-one term leaves the normally convergent
series over denominators at least two. The continued zero-order arithmetic
term is not part of `vacuumHigherKernel` and is not estimated here.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped Real

/-- The actual higher-order vacuum after removing its leading denominator. -/
def vacuumHigherRemainder (a e : ℝ) (j : ℤ) : ℂ :=
  vacuumHigherKernel a e j - (vacuumLeading a e j : ℂ)

/-- The remainder is the convergent tail, including the exact four seed signs. -/
theorem vacuumHigherRemainder_eq_tsum (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) :
    vacuumHigherRemainder a e j = ∑' n : ℕ, vacuumHigherTerm a e j (n + 1) := by
  have h := (summable_vacuumHigherTerm a e j).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at h
  rw [vacuumHigherTerm_zero_eq_ofReal a e j ha he] at h
  unfold vacuumHigherRemainder
  rw [vacuumHigherKernel_eq_tsum]
  linear_combination -h

/-- Removing the first denominator retains absolute convergence. -/
theorem summable_norm_vacuumHigherTerm_tail (a e : ℝ) (j : ℤ) :
    Summable (fun n : ℕ => ‖vacuumHigherTerm a e j (n + 1)‖) :=
  (summable_nat_add_iff 1).mpr (summable_vacuumHigherTerm a e j).norm

private theorem summable_tail_square :
    Summable (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2) := by
  convert (summable_nat_add_iff 1).mpr summable_one_div_nat_sq using 1
  ext n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  congr 2
  ring

private theorem tsum_tail_square_le_two :
    (∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  apply (Summable.tsum_le_tsum _ summable_tail_square summable_one_div_nat_sq).trans
    tsum_one_div_nat_sq_le_two
  intro n
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The exact four-seed summand has uniform denominator-square decay with the
sharp square-root exponential scale of its hyperbolic factors. -/
theorem norm_vacuumHigherTerm_le (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) (n : ℕ) :
    ‖vacuumHigherTerm a e j n‖ ≤
      32 * π ^ 2 * (a * e / ((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (4 * π * Real.sqrt (a * e) / ((n + 1 : ℕ) : ℝ)) := by
  have h0 := norm_higherKernelTerm_negative_le j 0 a e (-a) he
    (by simp; linarith) (by simp) (by simp; linarith) (by simp) n
  have hp := norm_higherKernelTerm_negative_le j 1 a e (1-a) he
    (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) (by norm_num) n
  have hm := norm_higherKernelTerm_negative_le j (-1) a e (1-a) he
    (by norm_num; linarith) (by norm_num)
    (by norm_num; linarith) (by norm_num; linarith) n
  have h2 := norm_higherKernelTerm_negative_le j 0 a e (2-a) he
    (by simp; linarith) (by simp)
    (by simp; linarith) (by simp) n
  push_cast at h0 hp hm h2
  have ht :
      ‖higherKernelTerm j 0 e (-a) n - higherKernelTerm j 1 e (1-a) n -
        higherKernelTerm j (-1) e (1-a) n + higherKernelTerm j 0 e (2-a) n‖ ≤
      ‖higherKernelTerm j 0 e (-a) n‖ + ‖higherKernelTerm j 1 e (1-a) n‖ +
        ‖higherKernelTerm j (-1) e (1-a) n‖ + ‖higherKernelTerm j 0 e (2-a) n‖ := by
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  calc
    _ = 2 * ‖higherKernelTerm j 0 e (-a) n - higherKernelTerm j 1 e (1-a) n -
        higherKernelTerm j (-1) e (1-a) n + higherKernelTerm j 0 e (2-a) n‖ := by
      simp [vacuumHigherTerm]
    _ ≤ 2 * (‖higherKernelTerm j 0 e (-a) n‖ + ‖higherKernelTerm j 1 e (1-a) n‖ +
        ‖higherKernelTerm j (-1) e (1-a) n‖ + ‖higherKernelTerm j 0 e (2-a) n‖) :=
      mul_le_mul_of_nonneg_left ht (by norm_num)
    _ ≤ 2 * (4 * π ^ 2 * (a * e / ((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (4 * π * Real.sqrt (a * e) / ((n + 1 : ℕ) : ℝ)) +
      4 * π ^ 2 * (a * e / ((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (4 * π * Real.sqrt (a * e) / ((n + 1 : ℕ) : ℝ)) +
      4 * π ^ 2 * (a * e / ((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (4 * π * Real.sqrt (a * e) / ((n + 1 : ℕ) : ℝ)) +
      4 * π ^ 2 * (a * e / ((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (4 * π * Real.sqrt (a * e) / ((n + 1 : ℕ) : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Nat.cast_add, Nat.cast_one] using
        add_le_add (add_le_add (add_le_add h0 hp) hm) h2
    _ = _ := by ring

/-- Every denominator in the remainder is at least two, reducing the exponent. -/
theorem norm_vacuumHigherTerm_tail_le (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) (n : ℕ) :
    ‖vacuumHigherTerm a e j (n + 1)‖ ≤
      (32 * π ^ 2 * (a * e) * Real.exp (2 * π * Real.sqrt (a * e))) *
        (1 / ((n + 2 : ℕ) : ℝ) ^ 2) := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have ha0 : 0 ≤ a := by linarith
  have hexp : 4 * π * Real.sqrt (a * e) / ((n + 2 : ℕ) : ℝ) ≤
      2 * π * Real.sqrt (a * e) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hd : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 2 n
    nlinarith [mul_le_mul_of_nonneg_left hd
      (show 0 ≤ 2 * π * Real.sqrt (a * e) by positivity)]
  calc
    _ ≤ 32 * π ^ 2 * (a * e / ((n + 2 : ℕ) : ℝ) ^ 2) *
        Real.exp (4 * π * Real.sqrt (a * e) / ((n + 2 : ℕ) : ℝ)) := by
      simpa only [Nat.add_assoc] using norm_vacuumHigherTerm_le a e j ha he (n + 1)
    _ ≤ 32 * π ^ 2 * (a * e / ((n + 2 : ℕ) : ℝ) ^ 2) *
        Real.exp (2 * π * Real.sqrt (a * e)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
        (by positivity)
    _ = _ := by ring

/-- C5's exponential remainder estimate for the actual higher-order series.
The separately continued zero-order term still requires its arithmetic bound. -/
theorem norm_vacuumHigherRemainder_le (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) :
    ‖vacuumHigherRemainder a e j‖ ≤
      64 * π ^ 2 * (a * e) * Real.exp (2 * π * Real.sqrt (a * e)) := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have ha0 : 0 ≤ a := by linarith
  rw [vacuumHigherRemainder_eq_tsum a e j ha he]
  calc
    _ ≤ ∑' n : ℕ, ‖vacuumHigherTerm a e j (n + 1)‖ :=
      norm_tsum_le_tsum_norm (summable_norm_vacuumHigherTerm_tail a e j)
    _ ≤ ∑' n : ℕ,
        (32 * π ^ 2 * (a * e) * Real.exp (2 * π * Real.sqrt (a * e))) *
          (1 / ((n + 2 : ℕ) : ℝ) ^ 2) :=
      Summable.tsum_le_tsum (norm_vacuumHigherTerm_tail_le a e j ha he)
        (summable_norm_vacuumHigherTerm_tail a e j) (summable_tail_square.mul_left _)
    _ = (32 * π ^ 2 * (a * e) * Real.exp (2 * π * Real.sqrt (a * e))) *
        (∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ 2) := tsum_mul_left
    _ ≤ (32 * π ^ 2 * (a * e) * Real.exp (2 * π * Real.sqrt (a * e))) * 2 :=
      mul_le_mul_of_nonneg_left tsum_tail_square_le_two (by positivity)
    _ = _ := by ring

/-- Expanded endpoint, directly comparing the actual higher kernel and leading term. -/
theorem norm_vacuumHigherKernel_sub_le (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) :
    ‖vacuumHigherKernel a e j - (vacuumLeading a e j : ℂ)‖ ≤
      64 * π ^ 2 * (a * e) * Real.exp (2 * π * Real.sqrt (a * e)) :=
  norm_vacuumHigherRemainder_le a e j ha he

end GapFamily.Analytic
