import GapFamily.Analytic.Bessel.BesselBasic

/-!
# Lower estimate near the endpoint of the Bessel integral

For `t ≥ 1`, the interval `0 < w ≤ 1/t` has length `1/t`, the numerator is at
least `exp(-1)`, and the denominator is at most `sqrt(3/t)`.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

/-- A positive constant lower bound on the interval of width `1/t`. -/
theorem besselK0ShiftIntegrand_lower {t w : ℝ} (ht : 1 ≤ t)
    (hw : w ∈ Ioc 0 (1 / t)) :
    Real.exp (-1) / Real.sqrt (3 / t) ≤ besselK0ShiftIntegrand t w := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hw0 : 0 < w := hw.1
  have hw1 : w ≤ 1 := hw.2.trans ((div_le_one ht0).mpr ht)
  have hden : w * (w + 2) ≤ 3 / t := by
    calc
      _ ≤ (1 / t) * 3 := mul_le_mul hw.2 (by linarith) (by linarith) (by positivity)
      _ = _ := by ring
  have hden0 : 0 < Real.sqrt (w * (w + 2)) := Real.sqrt_pos.mpr (by positivity)
  have hexp : Real.exp (-1) ≤ Real.exp (-t * w) := by
    apply Real.exp_le_exp.mpr
    have htw := (le_div_iff₀ ht0).mp hw.2
    nlinarith
  unfold besselK0ShiftIntegrand
  calc
    _ ≤ Real.exp (-1) / Real.sqrt (w * (w + 2)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hden0 (Real.sqrt_le_sqrt hden)
    _ ≤ _ := div_le_div_of_nonneg_right hexp (Real.sqrt_nonneg _)

/-- The interval length and the denominator scale combine into `t^(-1/2)`. -/
theorem besselK0Shift_lower_constant_integral {t : ℝ} (ht : 0 < t) :
    (∫ _ : ℝ in Ioc 0 (1 / t), Real.exp (-1) / Real.sqrt (3 / t)) =
      Real.exp (-1) / (Real.sqrt 3 * Real.sqrt t) := by
  rw [setIntegral_const, Real.volume_real_Ioc, sub_zero,
    max_eq_left (by positivity), smul_eq_mul, Real.sqrt_div (by norm_num)]
  field_simp [Real.sqrt_ne_zero'.mpr ht, Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<3), ht.ne']
  nlinarith [Real.sq_sqrt ht.le]

end GapFamily.Analytic
