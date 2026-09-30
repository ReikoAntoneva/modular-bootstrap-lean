import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Boltzmann loss for the square-root reference exponent

The tangent bound for the square root retains a linear loss in the removed
energy. On an upper bounded energy-to-charge interval the coefficient has a
fixed positive lower bound, independently of the charge.
-/

noncomputable section

open Real

namespace BTZEntropy.Comparison

set_option autoImplicit false

/-- The tangent inequality at a positive energy, including the zero endpoint
after removing energy. -/
theorem sqrt_sub_le_tangent {X q : ℝ} (hX : 0 < X) (hqX : q ≤ X) :
    sqrt (X - q) ≤ sqrt X - q / (2 * sqrt X) := by
  have hsX := sq_sqrt hX.le
  have hsq := sq_sqrt (sub_nonneg.mpr hqX)
  have hden : 0 < 2 * sqrt X := by positivity
  have hprod : sqrt (X - q) * (2 * sqrt X) ≤ 2 * X - q := by
    nlinarith [sq_nonneg (sqrt X - sqrt (X - q))]
  calc
    sqrt (X - q) ≤ (2 * X - q) / (2 * sqrt X) :=
      (le_div_iff₀ hden).mpr hprod
    _ = sqrt X - q / (2 * sqrt X) := by
      field_simp
      nlinarith

/-- The sharp tangent loss for the BTZ square-root exponent. -/
theorem referenceExponent_sub_le {a X q : ℝ}
    (ha : 0 ≤ a) (hX : 0 < X) (hqX : q ≤ X) :
    4 * Real.pi * sqrt (a * (X - q)) ≤
      4 * Real.pi * sqrt (a * X) - (2 * Real.pi * sqrt a / sqrt X) * q := by
  rw [sqrt_mul ha, sqrt_mul ha]
  have h := mul_le_mul_of_nonneg_left (sqrt_sub_le_tangent hX hqX)
    (show 0 ≤ 4 * Real.pi * sqrt a by positivity)
  convert h using 1 <;> ring

/-- The exponential form of the sharp tangent loss. -/
theorem referenceExp_sub_le {a X q : ℝ}
    (ha : 0 ≤ a) (hX : 0 < X) (hqX : q ≤ X) :
    exp (4 * Real.pi * sqrt (a * (X - q))) ≤
      exp (4 * Real.pi * sqrt (a * X)) * exp (-(2 * Real.pi * sqrt a / sqrt X) * q) := by
  rw [← exp_add]
  apply exp_le_exp.mpr
  convert referenceExponent_sub_le ha hX hqX using 1
  ring

/-- The tangent coefficient has a charge-independent positive lower bound
when `X / a` is bounded above. -/
theorem referenceBoltzmann_coefficient_ge {a X U : ℝ}
    (ha : 0 < a) (hX : 0 < X) (hU : 0 < U) (hXU : X ≤ U * a) :
    2 * Real.pi / sqrt U ≤ 2 * Real.pi * sqrt a / sqrt X := by
  have hroot : sqrt X ≤ sqrt U * sqrt a := by
    calc
      sqrt X ≤ sqrt (a * U) := sqrt_le_sqrt (by simpa only [mul_comm] using hXU)
      _ = sqrt U * sqrt a := by rw [sqrt_mul ha.le, mul_comm]
  apply (div_le_div_iff₀ (sqrt_pos.mpr hU) (sqrt_pos.mpr hX)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2 * Real.pi by positivity)]

/-- A fixed Boltzmann loss for every nonnegative removed energy. -/
theorem referenceExponent_sub_le_uniform {a X U q : ℝ}
    (ha : 0 < a) (hX : 0 < X) (hU : 0 < U) (hXU : X ≤ U * a)
    (hq : 0 ≤ q) (hqX : q ≤ X) :
    4 * Real.pi * sqrt (a * (X - q)) ≤
      4 * Real.pi * sqrt (a * X) - (2 * Real.pi / sqrt U) * q := by
  have h := referenceExponent_sub_le ha.le hX hqX
  have hc := mul_le_mul_of_nonneg_right
    (referenceBoltzmann_coefficient_ge ha hX hU hXU) hq
  linarith

/-- A charge-independent exponential weight for the removed energy. -/
theorem referenceExp_sub_le_uniform {a X U q : ℝ}
    (ha : 0 < a) (hX : 0 < X) (hU : 0 < U) (hXU : X ≤ U * a)
    (hq : 0 ≤ q) (hqX : q ≤ X) :
    exp (4 * Real.pi * sqrt (a * (X - q))) ≤
      exp (4 * Real.pi * sqrt (a * X)) * exp (-(2 * Real.pi / sqrt U) * q) := by
  rw [← exp_add]
  apply exp_le_exp.mpr
  convert referenceExponent_sub_le_uniform ha hX hU hXU hq hqX using 1
  ring

end BTZEntropy.Comparison
