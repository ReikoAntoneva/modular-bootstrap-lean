import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-! A positive observation height with a fixed compact range of nonzero Fourier arguments. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCentralFactor
open Set

/-- The actual frequency-dependent observation height. -/
def frequencyHeight (j : ℤ) : ℝ := 1 / (1 + |(j : ℝ)|)

/-- The observation height is positive even at zero frequency. -/
theorem frequencyHeight_pos (j : ℤ) : 0 < frequencyHeight j := by
  unfold frequencyHeight
  positivity

/-- A nonzero integer frequency has real absolute value at least one. -/
theorem one_le_abs_frequency {j : ℤ} (hj : j ≠ 0) : 1 ≤ |(j : ℝ)| := by
  exact_mod_cast Int.one_le_abs hj

/-- Every nonzero frequency gives a Bessel argument in the same fixed compact interval. -/
theorem frequencyHeight_argument_mem {j : ℤ} (hj : j ≠ 0) :
    2 * Real.pi * |(j : ℝ)| * frequencyHeight j ∈ Icc Real.pi (2 * Real.pi) := by
  have hn := one_le_abs_frequency hj
  have hd : 0 < 1 + |(j : ℝ)| := by positivity
  simp only [frequencyHeight, mul_one_div, mem_Icc]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hn)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [Real.pi_pos]

/-- The reciprocal square-root normalization is an exact positive real identity. -/
theorem inv_sqrt_frequencyHeight (j : ℤ) :
    (Real.sqrt (frequencyHeight j))⁻¹ = Real.sqrt (1 + |(j : ℝ)|) := by
  rw [frequencyHeight, one_div, Real.sqrt_inv, inv_inv]

/-- Positive real frequency powers have their literal principal complex-power norm. -/
theorem norm_frequency_cpow {j : ℤ} (hj : j ≠ 0) (κ : ℂ) :
    ‖((|(j : ℝ)| : ℝ) : ℂ) ^ κ‖ = |(j : ℝ)| ^ κ.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos
    (lt_of_lt_of_le zero_lt_one (one_le_abs_frequency hj)) κ

/-- The inverse frequency-power norm has the exact negative real exponent. -/
theorem norm_inv_frequency_cpow {j : ℤ} (hj : j ≠ 0) (κ : ℂ) :
    ‖(((|(j : ℝ)| : ℝ) : ℂ) ^ κ)⁻¹‖ = |(j : ℝ)| ^ (-κ.re) := by
  rw [norm_inv, norm_frequency_cpow hj, Real.rpow_neg (abs_nonneg _)]

end GapFamily.Analytic.PoincareCentralFactor
