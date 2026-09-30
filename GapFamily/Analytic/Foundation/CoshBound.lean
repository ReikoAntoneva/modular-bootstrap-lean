import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Vanishing hyperbolic cosine bound

The quadratic bound retains the zero of the higher-order kernel at zero
seed energy and preserves the sum of the chiral exponential arguments.
-/

namespace GapFamily.Analytic

/-- Exponential growth with the linear zero of the hyperbolic sine retained. -/
theorem sinh_le_mul_exp (x : ℝ) :
    Real.sinh x ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-2 * x))
    (Real.exp_pos x).le
  have he : Real.exp x * Real.exp (-2 * x) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  rw [Real.sinh_eq]
  nlinarith

/-- A hyperbolic cosine remainder bound retaining its quadratic zero. -/
theorem cosh_sub_one_le {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh x - 1 ≤ x ^ 2 / 2 * Real.exp x := by
  have hs := sinh_le_mul_exp (x / 2)
  have hs0 : 0 ≤ Real.sinh (x / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hsq : Real.sinh (x / 2) ^ 2 ≤ (x / 2 * Real.exp (x / 2)) ^ 2 :=
    pow_le_pow_left₀ hs0 hs 2
  have he : Real.exp (x / 2) ^ 2 = Real.exp x := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hc : Real.cosh x = 2 * Real.sinh (x / 2) ^ 2 + 1 := by
    have h := Real.cosh_two_mul (x := x / 2)
    rw [show 2 * (x / 2) = x by ring, Real.cosh_sq] at h
    linarith
  rw [mul_pow, he] at hsq
  nlinarith

/-- On the positive axis a hyperbolic cosine is bounded by its growing exponential. -/
theorem cosh_le_exp {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  have hs : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx
  linarith [Real.cosh_add_sinh x]

/-- The product remainder is nonnegative without any sign restriction. -/
theorem cosh_mul_cosh_sub_one_nonneg (x y : ℝ) :
    0 ≤ Real.cosh x * Real.cosh y - 1 := by
  have h := mul_le_mul (Real.one_le_cosh x) (Real.one_le_cosh y)
    (by norm_num : (0 : ℝ) ≤ 1) (Real.cosh_pos x).le
  linarith

/-- A product remainder bound with its quadratic zero and exact exponent retained. -/
theorem cosh_mul_cosh_sub_one_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.cosh x * Real.cosh y - 1 ≤
      (x ^ 2 + y ^ 2) / 2 * Real.exp (x + y) := by
  have hfirst := mul_le_mul (cosh_sub_one_le hx) (cosh_le_exp hy)
    (Real.cosh_pos y).le (by positivity : 0 ≤ x ^ 2 / 2 * Real.exp x)
  have hsecond : Real.cosh y - 1 ≤ y ^ 2 / 2 * Real.exp (x + y) := by
    calc
      _ ≤ y ^ 2 / 2 * Real.exp y := cosh_sub_one_le hy
      _ ≤ y ^ 2 / 2 * Real.exp (x + y) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  rw [Real.exp_add] at hsecond ⊢
  nlinarith

/-- Absolute-value form of the quadratic product remainder estimate. -/
theorem cosh_mul_cosh_sub_one_abs_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.cosh x * Real.cosh y - 1| ≤
      (x ^ 2 + y ^ 2) / 2 * Real.exp (x + y) := by
  rw [abs_of_nonneg (cosh_mul_cosh_sub_one_nonneg x y)]
  exact cosh_mul_cosh_sub_one_le hx hy

end GapFamily.Analytic
