import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Elementary geometric decay for the remainder after cancellation of the
first finitely many moments.
-/

namespace GapFamily.Analytic

/-- A geometric ratio at most one half absorbs the remaining denominator. -/
theorem geometricMomentRemainder_le_pow (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / 2) (k : ℕ) :
    θ ^ (k + 1) / (1 - θ) ≤ θ ^ k := by
  apply (div_le_iff₀ (show 0 < 1 - θ by linarith)).2
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hθ0 k)

/-- Every ratio in the closed half interval has a uniform geometric remainder. -/
theorem geometricMomentRemainder_le_half_pow (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / 2) (k : ℕ) :
    θ ^ (k + 1) / (1 - θ) ≤ (1 / 2 : ℝ) ^ k :=
  (geometricMomentRemainder_le_pow θ hθ0 hθ k).trans
    (pow_le_pow_left₀ hθ0 hθ k)

/-- The uniform dyadic factor is an exponential with explicit positive rate. -/
theorem half_pow_eq_exp_neg_mul_log_two (k : ℕ) :
    (1 / 2 : ℝ) ^ k = Real.exp (-(k : ℝ) * Real.log 2) := by
  rw [show -(k : ℝ) * Real.log 2 = (k : ℝ) * (-Real.log 2) by ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- The geometric moment remainder decays exponentially in the moment count. -/
theorem geometricMomentRemainder_le_exp (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / 2) (k : ℕ) :
    θ ^ (k + 1) / (1 - θ) ≤ Real.exp (-(k : ℝ) * Real.log 2) := by
  rw [← half_pow_eq_exp_neg_mul_log_two]
  exact geometricMomentRemainder_le_half_pow θ hθ0 hθ k

end GapFamily.Analytic
