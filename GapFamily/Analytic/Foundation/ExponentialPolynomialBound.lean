import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial absorption into an exponential

An explicit increase of the exponential rate absorbs a nonnegative coefficient
and any natural power on the range starting at one.
-/

namespace GapFamily.Analytic

/-- A polynomial factor can be absorbed by increasing the exponential rate.
The original rate `D` may have either sign. -/
theorem polynomial_mul_exp_le_exp {A B D : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (n : ℕ) :
    A * B ^ n * Real.exp (D * B) ≤ Real.exp ((A + D + (n : ℝ)) * B) := by
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hcoeff : A ≤ Real.exp (A * B) := by
    calc
      A ≤ A * B := le_mul_of_one_le_right hA hB
      _ ≤ A * B + 1 := le_add_of_nonneg_right zero_le_one
      _ ≤ Real.exp (A * B) := Real.add_one_le_exp (A * B)
  have hpower : B ^ n ≤ Real.exp ((n : ℝ) * B) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hB0 (by linarith [Real.add_one_le_exp B]) n
  calc
    A * B ^ n * Real.exp (D * B) ≤
        Real.exp (A * B) * Real.exp ((n : ℝ) * B) * Real.exp (D * B) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hcoeff hpower (pow_nonneg hB0 n) (Real.exp_pos _).le)
        (Real.exp_pos _).le
    _ = Real.exp ((A + D + (n : ℝ)) * B) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end GapFamily.Analytic
