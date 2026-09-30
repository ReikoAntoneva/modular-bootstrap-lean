import GapFamily.Analytic.Bessel.BesselBasic

/-!
# Ordinary integrability and the upper Bessel bound

The endpoint singularity of the shifted order-zero Bessel integrand is
dominated by the ordinary Gamma density of exponent `-1/2`.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

/-- The shifted Bessel integrand has the inverse square-root Gamma majorant. -/
theorem besselK0ShiftIntegrand_le_gamma (t w : ℝ) (hw : 0 < w) :
    besselK0ShiftIntegrand t w ≤
      (1 / Real.sqrt 2) * (w ^ (-(1 / 2 : ℝ)) * Real.exp (-t * w)) := by
  have hpow : w ^ (-(1 / 2 : ℝ)) = (Real.sqrt w)⁻¹ := by
    rw [Real.rpow_neg hw.le, ← Real.sqrt_eq_rpow]
  have hden : 0 < Real.sqrt 2 * Real.sqrt w := by positivity
  have hcmp : Real.sqrt 2 * Real.sqrt w ≤ Real.sqrt (w * (w + 2)) := by
    rw [Real.sqrt_mul hw.le]
    have hroot : Real.sqrt 2 ≤ Real.sqrt (w + 2) :=
      Real.sqrt_le_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg w]
  unfold besselK0ShiftIntegrand
  rw [hpow]
  calc
    Real.exp (-t * w) / Real.sqrt (w * (w + 2)) ≤
        Real.exp (-t * w) / (Real.sqrt 2 * Real.sqrt w) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hden hcmp
    _ = (1 / Real.sqrt 2) * ((Real.sqrt w)⁻¹ * Real.exp (-t * w)) := by ring

/-- The inverse square-root Gamma majorant is ordinarily integrable. -/
theorem besselK0_majorant_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun w : ℝ =>
      (1 / Real.sqrt 2) * (w ^ (-(1 / 2 : ℝ)) * Real.exp (-t * w))) (Ioi 0) := by
  have h : IntegrableOn (fun w : ℝ =>
      w ^ (-(1 / 2 : ℝ)) * Real.exp (-t * w)) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2 : ℝ))
        (b := t) (by norm_num) (by norm_num) ht)
  exact h.const_mul _

/-- The Gamma majorant has the exact square-root integral. -/
theorem besselK0_majorant_integral {t : ℝ} (ht : 0 < t) :
    (∫ w : ℝ in Ioi 0,
      (1 / Real.sqrt 2) * (w ^ (-(1 / 2 : ℝ)) * Real.exp (-t * w))) =
      Real.sqrt Real.pi / (Real.sqrt 2 * Real.sqrt t) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 1 / 2) (r := t) (by norm_num) ht
  norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
    neg_mul] at h
  simp only [neg_mul]
  rw [integral_const_mul, h, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow,
    Real.sqrt_div (by positivity), Real.sqrt_one]
  ring

/-- Ordinary integrability includes the singular endpoint and infinite tail. -/
theorem besselK0ShiftIntegrand_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (besselK0ShiftIntegrand t) (Ioi 0) := by
  apply (besselK0_majorant_integrable ht).mono_nonneg
  · have h : Measurable (besselK0ShiftIntegrand t) := by
      unfold besselK0ShiftIntegrand
      fun_prop
    exact h.aestronglyMeasurable
  · filter_upwards with w
    unfold besselK0ShiftIntegrand
    positivity
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact besselK0ShiftIntegrand_le_gamma t w hw

/-- The actual shifted Bessel integral is bounded by its exact Gamma majorant. -/
theorem besselK0Shift_integral_le {t : ℝ} (ht : 0 < t) :
    (∫ w : ℝ in Ioi 0, besselK0ShiftIntegrand t w) ≤
      Real.sqrt Real.pi / (Real.sqrt 2 * Real.sqrt t) := by
  rw [← besselK0_majorant_integral ht]
  exact setIntegral_mono_on (besselK0ShiftIntegrand_integrable ht)
    (besselK0_majorant_integrable ht) measurableSet_Ioi
    (fun w hw => besselK0ShiftIntegrand_le_gamma t w hw)

end GapFamily.Analytic
