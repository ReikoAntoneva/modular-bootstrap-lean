import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exponential lower bound for the hyperbolic sine

The factor retains its linear zero at the origin while recovering a fixed
fraction of its exponential growth. This estimate is used in the vacuum
factorization on the physical cone.
-/

namespace GapFamily.Analytic

/-- A hyperbolic sine lower bound retaining its zero and almost its full exponent. -/
theorem mul_exp_le_sinh {r : ℝ} (hr : 0 ≤ r) :
    r / 100 * Real.exp ((19 / 20 : ℝ) * r) ≤ Real.sinh r := by
  by_cases hsmall : r ≤ 1
  · have hexp : Real.exp ((19 / 20 : ℝ) * r) ≤ 100 := by
      have h := Real.exp_le_exp.mpr (show (19 / 20 : ℝ) * r ≤ 1 by linarith)
      linarith [Real.exp_one_lt_three]
    calc
      _ ≤ r / 100 * 100 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = r := by ring
      _ ≤ Real.sinh r := Real.self_le_sinh_iff.mpr hr
  · have hone : 1 ≤ r := le_of_lt (lt_of_not_ge hsmall)
    have hneg : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hlarge : 2 ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
    have hquarter : Real.exp r / 4 ≤ Real.sinh r := by
      rw [Real.sinh_eq]
      linarith
    have hlin : r / 20 ≤ Real.exp (r / 20) := by
      linarith [Real.add_one_le_exp (r / 20)]
    calc
      _ ≤ (Real.exp (r / 20) / 5) * Real.exp ((19 / 20 : ℝ) * r) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith
      _ = Real.exp r / 5 := by
        rw [div_mul_eq_mul_div, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp r / 4 := by linarith [Real.exp_pos r]
      _ ≤ Real.sinh r := hquarter

end GapFamily.Analytic
