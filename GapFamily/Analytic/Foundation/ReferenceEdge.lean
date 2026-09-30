import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Ordinary integrability at a nonzero-spin threshold

The reference measure in a nonzero-spin sector has density
`1 / sqrt (E^2 - r^2)` above the threshold `r = |j| > 0`.
Factoring the radicand exhibits an integrable inverse square-root singularity
times a continuous bounded factor. Thus the open edge carries finite ordinary
mass on each bounded interval, including when a continuous numerator is present.
-/

namespace GapFamily.Analytic

open Real Set MeasureTheory

/-- Factorization of the reference density above a positive threshold. -/
theorem nonzero_edge_density_eq {r E : ℝ} (hE : r < E) :
    1 / Real.sqrt (E ^ 2 - r ^ 2) =
      (E - r) ^ (-(1 / 2 : ℝ)) * (Real.sqrt (E + r))⁻¹ := by
  rw [show E ^ 2 - r ^ 2 = (E - r) * (E + r) by ring,
    Real.sqrt_mul (sub_nonneg.mpr hE.le), one_div, mul_inv,
    Real.rpow_neg (sub_nonneg.mpr hE.le), ← Real.sqrt_eq_rpow]

/-- The singular factor is integrable on every bounded interval above its edge. -/
theorem shifted_inverse_sqrt_integrableOn (r B : ℝ) :
    IntegrableOn (fun E : ℝ => (E - r) ^ (-(1 / 2 : ℝ))) (Ioo r B) := by
  by_cases h : r ≤ B
  · have hp := (intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := B - r) (by norm_num : -1 < -(1 / 2 : ℝ))).comp_sub_right r
    have hp' : IntervalIntegrable
        (fun E : ℝ => (E - r) ^ (-(1 / 2 : ℝ))) volume r B := by
      simpa only [zero_add, sub_add_cancel] using hp
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le h).mp hp'
  · simp [Ioo_eq_empty_of_le (le_of_not_ge h)]

/-- Finite ordinary mass at the actual nonzero-spin square-root singularity. -/
theorem nonzero_edge_integrableOn {r B : ℝ} (hr : 0 < r) :
    IntegrableOn (fun E : ℝ => 1 / Real.sqrt (E ^ 2 - r ^ 2)) (Ioo r B) := by
  have hc : ContinuousOn (fun E : ℝ => (Real.sqrt (E + r))⁻¹) (Icc r B) := by
    apply ContinuousOn.inv₀ (Real.continuous_sqrt.comp
      (continuous_id.add continuous_const)).continuousOn
    intro E hE
    apply Real.sqrt_ne_zero'.mpr
    change 0 < E + r
    linarith [hE.1]
  have hi := (shifted_inverse_sqrt_integrableOn r B).mul_continuousOn_of_subset
    hc measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  exact hi.congr_fun (fun E hE => (nonzero_edge_density_eq hE.1).symm) measurableSet_Ioo

/-- A numerator continuous through a nonzero-spin edge remains ordinarily integrable. -/
theorem nonzero_edge_continuous_numerator_integrableOn {r B : ℝ} (hr : 0 < r)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc r B)) :
    IntegrableOn (fun E : ℝ => f E / Real.sqrt (E ^ 2 - r ^ 2)) (Ioo r B) := by
  have hi := (nonzero_edge_integrableOn (B := B) hr).mul_continuousOn_of_subset
    hf measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hi

end GapFamily.Analytic
