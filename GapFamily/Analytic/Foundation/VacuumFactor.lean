import GapFamily.Analytic.Foundation.SinhLower
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Chiral vacuum factor

The four denominator-one vacuum seeds contain the difference of the two
hyperbolic cosines defined here. Its lower bound retains the vanishing at
the chiral threshold. This module concerns the real factor alone.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped Real

/-- The chiral difference between the vacuum and its null subtraction. -/
def vacuumDifference (a t : ℝ) : ℝ :=
  Real.cosh (2 * π * Real.sqrt (a * t)) -
    Real.cosh (2 * π * Real.sqrt ((a - 2) * t))

@[simp] theorem vacuumDifference_zero (a : ℝ) : vacuumDifference a 0 = 0 := by
  simp [vacuumDifference]

/-- The exact factorization into a large and a small hyperbolic sine. -/
theorem vacuumDifference_eq_sinh {a t : ℝ} (ha : 2 ≤ a) :
    vacuumDifference a t =
      2 * Real.sinh (π * (Real.sqrt a + Real.sqrt (a - 2)) * Real.sqrt t) *
        Real.sinh (π * (Real.sqrt a - Real.sqrt (a - 2)) * Real.sqrt t) := by
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 0 ≤ a - 2 := by linarith
  unfold vacuumDifference
  rw [Real.sqrt_mul ha0, Real.sqrt_mul ha2]
  have hp : 2 * π * (Real.sqrt a * Real.sqrt t) =
      π * (Real.sqrt a + Real.sqrt (a - 2)) * Real.sqrt t +
        π * (Real.sqrt a - Real.sqrt (a - 2)) * Real.sqrt t := by ring
  have hm : 2 * π * (Real.sqrt (a - 2) * Real.sqrt t) =
      π * (Real.sqrt a + Real.sqrt (a - 2)) * Real.sqrt t -
        π * (Real.sqrt a - Real.sqrt (a - 2)) * Real.sqrt t := by ring
  rw [hp, hm, Real.cosh_add, Real.cosh_sub]
  ring

/-- Both factors have nonnegative arguments, including the spin threshold. -/
theorem vacuumDifference_nonneg {a t : ℝ} (ha : 2 ≤ a) :
    0 ≤ vacuumDifference a t := by
  rw [vacuumDifference_eq_sinh ha]
  have hs : Real.sqrt (a - 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr (by positivity)))
    (Real.sinh_nonneg_iff.mpr (mul_nonneg
      (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hs)) (Real.sqrt_nonneg t)))

/-- A simple upper bound valid even when the real input is not physical. -/
theorem vacuumDifference_le_exp (a t : ℝ) :
    vacuumDifference a t ≤ Real.exp (2 * π * Real.sqrt (a * t)) := by
  have hs : 0 ≤ Real.sinh (2 * π * Real.sqrt (a * t)) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hc := Real.cosh_pos (2 * π * Real.sqrt ((a - 2) * t))
  have he := Real.cosh_add_sinh (2 * π * Real.sqrt (a * t))
  unfold vacuumDifference
  linarith

/-- The quantitative lower bound preserves the factor of `t` at the edge. -/
theorem vacuumDifference_ge_exp {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    π ^ 2 / 25 * t *
      Real.exp ((19 / 20 : ℝ) * π * (Real.sqrt a + Real.sqrt (a - 2)) * Real.sqrt t) ≤
        vacuumDifference a t := by
  let A : ℝ := π * (Real.sqrt a + Real.sqrt (a - 2)) * Real.sqrt t
  let B : ℝ := π * (Real.sqrt a - Real.sqrt (a - 2)) * Real.sqrt t
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 0 ≤ a - 2 := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by
    have hs : Real.sqrt (a - 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
    exact mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hs))
      (Real.sqrt_nonneg t)
  have hAB : A * B = 2 * π ^ 2 * t := by
    calc
      A * B = π ^ 2 * ((Real.sqrt a) ^ 2 - (Real.sqrt (a - 2)) ^ 2) *
          (Real.sqrt t) ^ 2 := by dsimp [A, B]; ring
      _ = 2 * π ^ 2 * t := by
        rw [Real.sq_sqrt ha0, Real.sq_sqrt ha2, Real.sq_sqrt ht]
        ring
  have hmain := mul_le_mul (mul_exp_le_sinh hA) (Real.self_le_sinh_iff.mpr hB)
    hB (Real.sinh_nonneg_iff.mpr hA)
  rw [vacuumDifference_eq_sinh ha]
  change _ ≤ 2 * Real.sinh A * Real.sinh B
  calc
    _ = 2 * (A / 100 * Real.exp ((19 / 20 : ℝ) * A) * B) := by
      have he : (19 / 20 : ℝ) * π * (Real.sqrt a + Real.sqrt (a - 2)) * Real.sqrt t =
          (19 / 20 : ℝ) * A := by dsimp [A]; ring
      rw [he]
      calc
        _ = (A * B) / 50 * Real.exp ((19 / 20 : ℝ) * A) := by rw [hAB]; ring
        _ = _ := by ring
    _ ≤ 2 * (Real.sinh A * Real.sinh B) :=
      mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = _ := by ring

end GapFamily.Analytic
