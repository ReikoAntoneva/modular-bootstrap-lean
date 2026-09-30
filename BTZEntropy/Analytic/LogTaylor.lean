import BTZEntropy.Coefficient
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Quantitative real logarithm Taylor estimates, including order zero. -/

noncomputable section

open scoped BigOperators

namespace BTZEntropy

theorem abs_log_one_add_sub_sum_le_two {z : ℝ} (hz : |z| ≤ 1 / 2) (P : ℕ) :
    |Real.log (1 + z) - ∑ j ∈ Finset.range P,
      ((-1 : ℝ) ^ j / (j + 1 : ℕ)) * z ^ (j + 1)| ≤ 2 * |z| ^ (P + 1) := by
  have hsmall : |-z| < 1 := by rw [abs_neg]; linarith
  have h : |(∑ j ∈ Finset.range P, (-z) ^ (j + 1) / (j + 1 : ℕ)) +
      Real.log (1 - -z)| ≤ |-z| ^ (P + 1) / (1 - |-z|) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Real.abs_log_sub_add_sum_range_le hsmall P
  have hs : (∑ j ∈ Finset.range P, (-z) ^ (j + 1) / (j + 1 : ℕ)) =
      -(∑ j ∈ Finset.range P, ((-1 : ℝ) ^ j / (j + 1 : ℕ)) * z ^ (j + 1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [neg_eq_neg_one_mul, mul_pow, pow_succ (-1 : ℝ)]
    ring
  rw [hs, sub_neg_eq_add, abs_neg] at h
  have hden : 0 < 1 - |z| := by linarith
  calc
    _ = |-(∑ j ∈ Finset.range P,
        ((-1 : ℝ) ^ j / (j + 1 : ℕ)) * z ^ (j + 1)) + Real.log (1 + z)| := by
          congr 1
          ring
    _ ≤ |z| ^ (P + 1) / (1 - |z|) := h
    _ ≤ 2 * |z| ^ (P + 1) := by
      apply (div_le_iff₀ hden).2
      nlinarith [pow_nonneg (abs_nonneg z) (P + 1)]

/-- A uniform linear bound on the argument gives the full next-order
remainder for the finite logarithm Taylor polynomial. -/
theorem abs_log_one_add_sub_sum_le_power {z ε A : ℝ}
    (hz : |z| ≤ A * ε)
    (hsmall : A * ε ≤ 1 / 2) (P : ℕ) :
    |Real.log (1 + z) - ∑ j ∈ Finset.range P,
      ((-1 : ℝ) ^ j / (j + 1 : ℕ)) * z ^ (j + 1)| ≤
        (2 * A ^ (P + 1)) * ε ^ (P + 1) := by
  calc
    _ ≤ 2 * |z| ^ (P + 1) := abs_log_one_add_sub_sum_le_two (hz.trans hsmall) P
    _ ≤ 2 * (A * ε) ^ (P + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg z) hz _) (by norm_num)
    _ = _ := by rw [mul_pow]; ring

/-- A finite coefficient bound controls the count correction uniformly on
the interval from zero to one. No coefficient continuity is required. -/
theorem abs_count_correction_sum_le (u : ℕ → ℝ) (P : ℕ) {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : ∀ n, 1 ≤ n → n ≤ P → |u n| ≤ M) :
    |∑ j ∈ Finset.range P, u (j + 1) * ε ^ (j + 1)| ≤ (P * M) * ε := by
  calc
    _ ≤ ∑ j ∈ Finset.range P, |u (j + 1) * ε ^ (j + 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range P, M * ε := by
      apply Finset.sum_le_sum
      intro j hj
      have hp : ε ^ (j + 1) ≤ ε := by
        rw [pow_succ]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (pow_le_one₀ hε hε1) hε
      rw [abs_mul, abs_of_nonneg (pow_nonneg hε _)]
      exact mul_le_mul (hu (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega))
        hp (pow_nonneg hε _) hM
    _ = _ := by simp; ring

end BTZEntropy
