import GapFamily.Analytic.Kernel.FullKernelCoercivity
import GapFamily.Analytic.Kernel.FullKernelOperatorBound

/-!
# Exponential control of the propagation loss

The physical integer-row count and the enlarged operator bound absorb all
polynomial factors into one global positive exponential rate.
-/

noncomputable section

open Real

namespace GapFamily.Analytic

/-- A global rate controlling the actual quarter-power propagation loss. -/
def correctedPropagationLossExponent : ℝ :=
  100000 + correctedPropagationExponent + correctedIdentityPlusExponent + 2

theorem correctedPropagationLossExponent_pos : 0 < correctedPropagationLossExponent := by
  unfold correctedPropagationLossExponent
  have := correctedPropagationExponent_pos
  have := correctedIdentityPlusExponent_pos
  positivity

/-- The actual loss is at most exponential on every finite family of
distinct physical integer spin rows. -/
theorem correctedPropagationLoss_le_exp {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) {b : ℝ} (hb : 1 ≤ b)
    (hband : ∀ i, |(J i : ℝ)| < b) :
    correctedPropagationLoss J b ≤ exp (correctedPropagationLossExponent * b) := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hcard := physicalLowBand_card_le J hJ hb hband
  have hs : sqrt ‖correctedLowBandIdentityPlus J (4 * b)‖ ≤
      exp (correctedIdentityPlusExponent * b) := by
    calc
      _ ≤ sqrt (exp (correctedIdentityPlusExponent * b)) :=
        sqrt_le_sqrt (norm_correctedLowBandIdentityPlus_fourfold_le_exp J hJ hb hband)
      _ ≤ exp (correctedIdentityPlusExponent * b) :=
        sqrt_le_self_iff.mpr (Or.inr (one_le_exp_iff.mpr
          (mul_nonneg correctedIdentityPlusExponent_pos.le hb0)))
  unfold correctedPropagationLoss
  calc
    _ ≤ 20000 * (5 * b) * b * exp (correctedPropagationExponent * b) *
        exp (correctedIdentityPlusExponent * b) := by
      gcongr
    _ = 100000 * b ^ 2 * exp ((correctedPropagationExponent + correctedIdentityPlusExponent) * b) := by
      rw [add_mul, exp_add]
      ring
    _ ≤ exp (correctedPropagationLossExponent * b) := by
      simpa only [correctedPropagationLossExponent, Nat.cast_ofNat, add_assoc] using
        polynomial_mul_exp_le_exp (A := 100000)
          (D := correctedPropagationExponent + correctedIdentityPlusExponent) (by norm_num) hb 2

end GapFamily.Analytic
