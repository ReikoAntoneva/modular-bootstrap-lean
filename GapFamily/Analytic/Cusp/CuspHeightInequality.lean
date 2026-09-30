import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace GapFamily.Analytic

/-- The literal row maximum is controlled by the quadratic height denominator. -/
theorem cusp_row_height_denominator_bound (c d x y : ℝ)
    (hc : 1 ≤ |c|) (hx : |x| ≤ 1 / 2) (hy : 1 / 2 ≤ y) :
    max |c| |d| * y ≤ 2 * ((c * x + d) ^ 2 + c ^ 2 * y ^ 2) := by
  have hy0 : 0 ≤ y := by linarith
  have hyc : y ≤ |c| * y := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hy0
  have hcy : 1 / 2 ≤ |c| * y := hy.trans hyc
  have hquad : |c| * y ≤ 2 * (|c| * y) ^ 2 := by
    nlinarith [sq_nonneg (|c| * y - 1 / 2)]
  have hd : |d| ≤ |c * x + d| + |c| / 2 := by
    calc
      |d| = |(c * x + d) - c * x| := by congr 1; ring
      _ ≤ |c * x + d| + |c * x| := abs_sub _ _
      _ = |c * x + d| + |c| * |x| := by rw [abs_mul]
      _ ≤ |c * x + d| + |c| / 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg c)]
  have hdy : |d| * y ≤ |c * x + d| * y + (|c| * y) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hd hy0]
  have hprod : |c * x + d| * y ≤ |c * x + d| * (|c| * y) :=
    mul_le_mul_of_nonneg_left hyc (abs_nonneg _)
  have hden : (c * x + d) ^ 2 + c ^ 2 * y ^ 2 =
      |c * x + d| ^ 2 + (|c| * y) ^ 2 := by
    rw [sq_abs, mul_pow, sq_abs]
  rw [hden]
  rcases le_total |c| |d| with hcd | hdc
  · rw [max_eq_right hcd]
    nlinarith [sq_nonneg (|c * x + d| - |c| * y),
      sq_nonneg |c * x + d|, sq_nonneg (|c| * y)]
  · rw [max_eq_left hdc]
    nlinarith [sq_nonneg |c * x + d|]


end GapFamily.Analytic
