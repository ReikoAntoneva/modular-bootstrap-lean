import BTZEntropy.Coefficient
import Mathlib.Analysis.Complex.Basic

/-!
# Finite Taylor expansion of the reciprocal saddle phase

The reciprocal term has an exact finite geometric expansion. Its explicit
remainder is uniformly bounded in the disk of radius half the positive real
expansion point. No asymptotic or interchange-of-limits assumption is used.
-/

noncomputable section

open scoped BigOperators

namespace BTZEntropy

/-- The reciprocal Taylor polynomial through degree `N`. -/
def reciprocalTaylor (β w : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), (-w) ^ n / β ^ (n + 1)

/-- The exact remainder after degree `N`. -/
def reciprocalRemainder (β w : ℂ) (N : ℕ) : ℂ :=
  (-w) ^ (N + 1) / (β ^ (N + 1) * (β + w))

theorem reciprocalTaylor_succ (β w : ℂ) (N : ℕ) :
    reciprocalTaylor β w (N + 1) =
      reciprocalTaylor β w N + (-w) ^ (N + 1) / β ^ (N + 2) := by
  simp [reciprocalTaylor, Finset.sum_range_succ]

/-- Exact complex Taylor identity, valid away from both poles. -/
theorem reciprocal_eq_taylor_add_remainder {β w : ℂ} (hβ : β ≠ 0)
    (hw : β + w ≠ 0) (N : ℕ) :
    (β + w)⁻¹ = reciprocalTaylor β w N + reciprocalRemainder β w N := by
  induction N with
  | zero =>
      simp [reciprocalTaylor, reciprocalRemainder]
      field_simp
      ring
  | succ N ih =>
      rw [reciprocalTaylor_succ, ih]
      unfold reciprocalRemainder
      rw [show N + 1 + 1 = N + 2 by omega]
      field_simp
      ring

/-- The coefficient of degree `n` is the usual signed reciprocal power. -/
theorem reciprocalTaylor_eq_sum (β w : ℂ) (N : ℕ) :
    reciprocalTaylor β w N =
      ∑ n ∈ Finset.range (N + 1), ((-1 : ℂ) ^ n / β ^ (n + 1)) * w ^ n := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [neg_eq_neg_one_mul, mul_pow]
  ring

/-- A positive real expansion point stays uniformly away from zero in its half disk. -/
theorem half_le_norm_add {β : ℝ} (hβ : 0 < β) {w : ℂ} (hw : ‖w‖ ≤ β / 2) :
    β / 2 ≤ ‖(β : ℂ) + w‖ := by
  have ht := norm_sub_le ((β : ℂ) + w) w
  have hb : ‖(β : ℂ)‖ = β := by simp [abs_of_pos hβ]
  rw [add_sub_cancel_right, hb] at ht
  linarith

theorem reciprocalRemainder_norm_le {β : ℝ} (hβ : 0 < β) {w : ℂ}
    (hw : ‖w‖ ≤ β / 2) (N : ℕ) :
    ‖reciprocalRemainder β w N‖ ≤ 2 * ‖w‖ ^ (N + 1) / β ^ (N + 2) := by
  have hb : ‖(β : ℂ)‖ = β := by simp [abs_of_pos hβ]
  have hd := half_le_norm_add hβ hw
  have hp : 0 < β ^ (N + 1) := pow_pos hβ _
  simp only [reciprocalRemainder, norm_div, norm_pow, norm_neg, norm_mul, hb]
  calc
    ‖w‖ ^ (N + 1) / (β ^ (N + 1) * ‖(β : ℂ) + w‖) ≤
        ‖w‖ ^ (N + 1) / (β ^ (N + 1) * (β / 2)) := by
      exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg w) _)
        (mul_pos hp (by linarith)) (mul_le_mul_of_nonneg_left hd hp.le)
    _ = 2 * ‖w‖ ^ (N + 1) / β ^ (N + 2) := by
      rw [show N + 2 = (N + 1) + 1 by omega, pow_succ β (N + 1)]
      field_simp

/-- Multiplication by the phase constant preserves the explicit uniform remainder bound. -/
theorem phaseRemainder_norm_le (b : ℂ) {β : ℝ} (hβ : 0 < β) {w : ℂ}
    (hw : ‖w‖ ≤ β / 2) (N : ℕ) :
    ‖b * reciprocalRemainder β w N‖ ≤
      2 * ‖b‖ * ‖w‖ ^ (N + 1) / β ^ (N + 2) := by
  rw [norm_mul]
  calc
    ‖b‖ * ‖reciprocalRemainder β w N‖ ≤
        ‖b‖ * (2 * ‖w‖ ^ (N + 1) / β ^ (N + 2)) :=
      mul_le_mul_of_nonneg_left (reciprocalRemainder_norm_le hβ hw N) (norm_nonneg b)
    _ = _ := by ring

/-- Exact expansion of `x z + b / z`, including its finite remainder. -/
theorem saddlePhase_eq_taylor_add_remainder (x b β w : ℂ)
    (hβ : β ≠ 0) (hw : β + w ≠ 0) (N : ℕ) :
    x * (β + w) + b / (β + w) =
      x * β + x * w + b * reciprocalTaylor β w N + b * reciprocalRemainder β w N := by
  rw [div_eq_mul_inv, reciprocal_eq_taylor_add_remainder hβ hw]
  ring

end BTZEntropy
