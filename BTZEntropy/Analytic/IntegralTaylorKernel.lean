import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integral of the Taylor remainder kernel

The nonnegative scalar kernel has its exact factorial integral on the interval
joining zero to any real displacement.
-/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace BTZEntropy.Analytic

/-- Exact integral of the normalized Taylor kernel, for either sign of the displacement. -/
theorem integral_abs_taylorKernel (ε : ℝ) (N : ℕ) :
    (∫ s in min 0 ε..max 0 ε, |ε - s| ^ N / (N.factorial : ℝ)) =
      |ε| ^ (N + 1) / ((N + 1).factorial : ℝ) := by
  rw [intervalIntegral.integral_div]
  have hkernel : (∫ s in min 0 ε..max 0 ε, |ε - s| ^ N) =
      |ε| ^ (N + 1) / (N + 1) := by
    rw [integral_of_le (min_le_max)]
    have h := integral_pow_abs_sub_uIoc (a := ε) (b := 0) (n := N)
    simpa only [uIoc, min_comm ε 0, max_comm ε 0, abs_sub_comm ε,
      zero_sub, abs_neg] using h
  rw [hkernel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    div_div]

end BTZEntropy.Analytic
