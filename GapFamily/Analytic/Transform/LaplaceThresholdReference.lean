import GapFamily.Analytic.Foundation.ReferenceMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! The same-parameter cone density at one half is exactly the physical
reference measure, for ordinary scalar or Banach-valued integrals. -/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory

theorem referenceDensity_eq_cpow_one_half (J : ℤ) {E : ℝ} (hE : |(J : ℝ)| < E) :
    (referenceDensity J E : ℂ) = ((E ^ 2 - (J : ℝ) ^ 2 : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) := by
  have hE0 : 0 < E := (abs_nonneg _).trans_lt hE
  have hq : 0 < E ^ 2 - (J : ℝ) ^ 2 := by
    nlinarith [sq_abs (J : ℝ), (sq_lt_sq₀ (abs_nonneg (J : ℝ)) hE0.le).mpr hE]
  have hc := Complex.ofReal_cpow hq.le (-(1 / 2) : ℝ)
  norm_num only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] at hc
  rw [← hc, Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow]
  simp [referenceDensity, one_div]

theorem integrable_cpow_one_half_smul_iff_referenceMeasure
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (J : ℤ) (f : ℝ → H) :
    IntegrableOn (fun E : ℝ =>
      (((E ^ 2 - (J : ℝ) ^ 2 : ℝ) : ℂ) ^ (-(1 / 2) : ℂ)) • f E) (Ioi |(J : ℝ)|) ↔
      Integrable f (referenceMeasure J) := by
  rw [referenceMeasure, integrable_withDensity_iff_integrable_smul'
    (measurable_referenceDensity J).ennreal_ofReal (by simp)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
  rw [← referenceDensity_eq_cpow_one_half J hE,
    ENNReal.toReal_ofReal (referenceDensity_nonneg J E)]
  exact Complex.coe_smul _ _

theorem integral_cpow_one_half_smul_eq_referenceMeasure
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (J : ℤ) (f : ℝ → H) :
    (∫ E : ℝ in Ioi |(J : ℝ)|,
      (((E ^ 2 - (J : ℝ) ^ 2 : ℝ) : ℂ) ^ (-(1 / 2) : ℂ)) • f E) =
      ∫ E : ℝ, f E ∂referenceMeasure J := by
  rw [referenceMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_referenceDensity J).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
  rw [← referenceDensity_eq_cpow_one_half J hE,
    ENNReal.toReal_ofReal (referenceDensity_nonneg J E)]
  exact Complex.coe_smul _ _

end GapFamily.Analytic
