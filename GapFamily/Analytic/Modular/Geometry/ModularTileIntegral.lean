import GapFamily.Analytic.Modular.Geometry.ModularTileCoverage
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory
open scoped MatrixGroups Pointwise ENNReal

private theorem modularGroup_countable_integral : Countable SL(2, ℤ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := by
    change Countable (Fin 2 → Fin 2 → ℤ)
    infer_instance
  change Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1}
  infer_instance

/-- Transport of the ordinary integral from the chosen tile to its actual image. -/
theorem integral_modularAction_eq_tileIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UpperHalfPlane → E) (γ : SL(2, ℤ)) :
    (∫ τ : UpperHalfPlane, f (γ • τ) ∂modularMeasure) =
      ∫ τ : UpperHalfPlane in γ • ModularGroup.fd, f τ := by
  rw [← Set.image_smul]
  exact ((measurePreserving_modularAction γ).setIntegral_image_emb
    (measurableEmbedding_modularAction γ) f ModularGroup.fd).symm

/-- Each translated summand is integrable on the ordinary modular tile. -/
theorem integrable_modularAction_of_integrable
    {f : UpperHalfPlane → ℂ} (hf : Integrable f volume) (γ : SL(2, ℤ)) :
    Integrable (fun τ : UpperHalfPlane => f (γ • τ)) modularMeasure := by
  have he := measurableEmbedding_modularAction γ
  have hm := (measurePreserving_modularAction γ).restrict_image_emb he ModularGroup.fd
  simpa only [Function.comp_def, modularMeasure] using
    (hm.integrable_comp_emb he).mpr hf.integrableOn

/-- Global ordinary integrability controls the sum of all tile restrictions. -/
theorem integrable_sum_modular_tile_restrict
    {f : UpperHalfPlane → ℂ} (hf : Integrable f volume) :
    Integrable f (Measure.sum fun γ : SL(2, ℤ) =>
      (volume : Measure UpperHalfPlane).restrict (γ • ModularGroup.fd)) := by
  rw [sum_restrict_modular_tiles_eq_two_smul_volume]
  exact hf.smul_measure (by norm_num)

/-- The translated ordinary summands have summable integral norms. -/
theorem summable_integral_norm_modularAction
    {f : UpperHalfPlane → ℂ} (hf : Integrable f volume) :
    Summable (fun γ : SL(2, ℤ) =>
      ∫ τ : UpperHalfPlane, ‖f (γ • τ)‖ ∂modularMeasure) := by
  apply (integrable_sum_modular_tile_restrict hf).summable_integral.congr
  intro γ
  exact (integral_modularAction_eq_tileIntegral (fun τ => ‖f τ‖) γ).symm

/-- Unnormalized full-matrix periodization counts each ordinary point twice. -/
theorem integral_modularAction_tsum_eq_two_mul
    {f : UpperHalfPlane → ℂ} (hf : Integrable f volume) :
    (∫ τ : UpperHalfPlane, (∑' γ : SL(2, ℤ), f (γ • τ)) ∂modularMeasure) =
      (2 : ℂ) * (∫ τ : UpperHalfPlane, f τ) := by
  have : Countable SL(2, ℤ) := modularGroup_countable_integral
  rw [← integral_tsum_of_summable_integral_norm
    (fun γ => integrable_modularAction_of_integrable hf γ)
    (summable_integral_norm_modularAction hf)]
  simp_rw [integral_modularAction_eq_tileIntegral]
  rw [← integral_sum_measure (integrable_sum_modular_tile_restrict hf),
    sum_restrict_modular_tiles_eq_two_smul_volume, integral_smul_measure]
  norm_num [Complex.real_smul]

end GapFamily.Analytic
