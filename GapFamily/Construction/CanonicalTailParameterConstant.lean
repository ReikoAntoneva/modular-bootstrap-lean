import GapFamily.Construction.CanonicalTailRepairBudget

/-!
# Fixed parameter for the canonical tail repair

The moment multiplier is chosen once from the actual canonical repair
constants, before any discretization scale is chosen. The numerical charge
threshold is exactly one hundred.
-/

noncomputable section

open Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A positive integer chosen solely from the actual tail repair cost. -/
def canonicalTailMomentMultiplier : ℕ :=
  ⌈(tailRepairExponent canonicalRepairCellCoefficient canonicalRepairKernelExponent
    (4 * π + 14) 2 + 16) / log 2⌉₊ + 1

theorem canonicalTailMomentMultiplier_pos : 0 < canonicalTailMomentMultiplier := by
  unfold canonicalTailMomentMultiplier
  omega

/-- The fixed multiplier pays the exact canonical exterior repair cost. -/
theorem canonicalTailMomentMultiplier_budget :
    tailRepairExponent canonicalRepairCellCoefficient canonicalRepairKernelExponent
      (4 * π + 14) 2 + 16 ≤ (canonicalTailMomentMultiplier : ℝ) * log 2 := by
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  apply (div_le_iff₀ hlog).mp
  calc
    _ ≤ (⌈(tailRepairExponent canonicalRepairCellCoefficient canonicalRepairKernelExponent
        (4 * π + 14) 2 + 16) / log 2⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (canonicalTailMomentMultiplier : ℝ) := by
      unfold canonicalTailMomentMultiplier
      push_cast
      linarith

/-- One hundred suffices for every numerical charge inequality in the actual
short-cell exterior allowance. -/
def canonicalTailChargeThreshold : ℕ := 100

theorem canonicalTailChargeThreshold_ge_hundred : 100 ≤ canonicalTailChargeThreshold := le_rfl

theorem canonicalTailChargeThreshold_real_spec (a : ℝ)
    (ha : (canonicalTailChargeThreshold : ℝ) ≤ a) :
    4 * π + 4 ≤ 7 * sqrt a := by
  have ha100 : (100 : ℝ) ≤ a := ha
  have hs : 10 ≤ sqrt a := Real.le_sqrt_of_sq_le (by nlinarith)
  nlinarith [Real.pi_lt_four]

theorem canonicalTailChargeThreshold_spec (a : ℕ)
    (ha : canonicalTailChargeThreshold ≤ a) :
    4 * π + 4 ≤ 7 * sqrt (a : ℝ) :=
  canonicalTailChargeThreshold_real_spec a (by exact_mod_cast ha)

end GapFamily.Construction
