import GapFamily.Construction.RealInitialCell
import Mathlib.Analysis.SpecificLimits.Basic

/-! The initial moment degree at a processing endpoint fixed independently of
the central charge. Its growth is proportional to the square root of charge. -/

noncomputable section

open Real Filter

namespace BTZEntropy.Construction

def fixedBandDegree (a U : ℝ) : ℕ := ⌊sqrt (a * U)⌋₊

theorem fixedBandDegree_le_sqrt (a U : ℝ) :
    (fixedBandDegree a U : ℝ) ≤ sqrt (a * U) :=
  Nat.floor_le (sqrt_nonneg _)

theorem sqrt_lt_fixedBandDegree_add_one (a U : ℝ) :
    sqrt (a * U) < (fixedBandDegree a U : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem fixedBandDegree_half_sqrt {a U : ℝ} (hlarge : 2 ≤ sqrt (a * U)) :
    sqrt (a * U) / 2 ≤ (fixedBandDegree a U : ℝ) := by
  have h := sqrt_lt_fixedBandDegree_add_one a U
  linarith

/-- Charge is controlled by a quadratic polynomial in the rounded degree. -/
theorem fixedBandDegree_polynomial_base {a U : ℝ} (ha : 0 ≤ a) (hU : 0 < U) :
    1 + a ≤ (1 + 1 / U) * ((fixedBandDegree a U : ℝ) + 1) ^ 2 := by
  have hfloor := sqrt_lt_fixedBandDegree_add_one a U
  have hk : 0 ≤ (fixedBandDegree a U : ℝ) := Nat.cast_nonneg _
  have hsq : a * U ≤ ((fixedBandDegree a U : ℝ) + 1) ^ 2 := by
    nlinarith [sq_sqrt (mul_nonneg ha hU.le), sqrt_nonneg (a * U)]
  have ha' : a ≤ ((fixedBandDegree a U : ℝ) + 1) ^ 2 / U :=
    (le_div_iff₀ hU).mpr hsq
  have hone : 1 ≤ ((fixedBandDegree a U : ℝ) + 1) ^ 2 := by nlinarith
  calc
    1 + a ≤ ((fixedBandDegree a U : ℝ) + 1) ^ 2 +
        ((fixedBandDegree a U : ℝ) + 1) ^ 2 / U := add_le_add hone ha'
    _ = _ := by ring

/-- A sufficiently large but fixed processing endpoint dominates the signed
negative-mass exponent, uniformly in the charge. -/
theorem fixedBandDegree_negative_exponent {a b U C : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hU : 4 * C ^ 2 * b ≤ U) (hlarge : 2 ≤ sqrt (a * U)) :
    C * sqrt (a * b) ≤ (fixedBandDegree a U : ℝ) := by
  have hU0 : 0 ≤ U := (by positivity : 0 ≤ 4 * C ^ 2 * b).trans hU
  have hconstant : 2 * C * sqrt b ≤ sqrt U := by
    apply (le_sqrt (by positivity) hU0).mpr
    nlinarith [sq_sqrt hb]
  have hscale := mul_le_mul_of_nonneg_left hconstant (sqrt_nonneg a)
  have hhalf := fixedBandDegree_half_sqrt hlarge
  rw [sqrt_mul ha] at hhalf ⊢
  nlinarith only [hscale, hhalf]

theorem tendsto_fixedBandDegree_atTop {U : ℝ} (hU : 0 < U) :
    Tendsto (fun a : ℝ => fixedBandDegree a U) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (tendsto_sqrt_atTop.comp (tendsto_id.atTop_mul_const hU))

theorem eventually_fixedBandDegree_large {U : ℝ} (hU : 0 < U) (k₀ : ℕ) :
    ∀ᶠ a : ℝ in atTop, k₀ ≤ fixedBandDegree a U ∧ 2 ≤ sqrt (a * U) := by
  filter_upwards [(tendsto_fixedBandDegree_atTop hU).eventually_ge_atTop k₀,
    (tendsto_sqrt_atTop.comp (tendsto_id.atTop_mul_const hU)).eventually_ge_atTop 2]
    with a hk hroot
  exact ⟨hk, hroot⟩

end BTZEntropy.Construction
