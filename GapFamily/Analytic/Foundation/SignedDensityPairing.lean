import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Ordinary pairing against a signed density

An integrable real density defines a signed measure whose bounded measurable pairings
are ordinary integrals. Its total variation is exactly the integral of the absolute
density, and it introduces no atoms over an atomless reference measure.
-/

open MeasureTheory Set

namespace GapFamily.Analytic

private theorem integrable_density_mul_of_norm_bdd {μ : Measure ℝ} {q f : ℝ → ℝ}
    {C : ℝ} (hq : Integrable q μ) (hf : AEStronglyMeasurable f μ)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Integrable (fun x => q x * f x) μ := by
  refine (hq.norm.mul_const |C|).mono' (hq.aestronglyMeasurable.mul hf) ?_
  filter_upwards [hbound] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hx.trans (le_abs_self C)) (norm_nonneg (q x))

/-- A bounded measurable test function is integrable against the signed density,
and its signed integral equals the ordinary density-weighted integral. -/
theorem signedDensity_pairing_of_norm_bdd {μ : Measure ℝ} {q f : ℝ → ℝ}
    {C : ℝ} (hq : Integrable q μ) (hf : AEStronglyMeasurable f μ)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    (μ.withDensityᵥ q).Integrable f ∧
      Integrable (fun x => q x * f x) μ ∧
      (∫ᵛ x, f x ∂<•μ.withDensityᵥ q) = ∫ x, q x * f x ∂μ := by
  have hqn : Integrable (fun x => -q x) μ := by
    exact hq.neg.congr (Filter.Eventually.of_forall (fun _ => rfl))
  have hpos : Integrable (fun x => (ENNReal.ofReal (q x)).toReal * f x) μ := by
    simpa only [ENNReal.toReal_ofReal'] using
      integrable_density_mul_of_norm_bdd hq.pos_part hf hbound
  have hneg : Integrable (fun x => (ENNReal.ofReal (-q x)).toReal * f x) μ := by
    simpa only [ENNReal.toReal_ofReal'] using
      integrable_density_mul_of_norm_bdd hqn.pos_part hf hbound
  have hposm : Integrable f (μ.withDensity (fun x => ENNReal.ofReal (q x))) := by
    rw [integrable_withDensity_iff_integrable_smul₀'
      hq.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [smul_eq_mul] using hpos
  have hnegm : Integrable f (μ.withDensity (fun x => ENNReal.ofReal (-q x))) := by
    rw [integrable_withDensity_iff_integrable_smul₀'
      hqn.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [smul_eq_mul] using hneg
  let : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (q x))) :=
    isFiniteMeasure_withDensity_ofReal hq.2
  let : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (-q x))) :=
    isFiniteMeasure_withDensity_ofReal hq.neg.2
  have hposv : (μ.withDensity (fun x => ENNReal.ofReal (q x))).toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hposm
  have hnegv : (μ.withDensity (fun x => ENNReal.ofReal (-q x))).toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hnegm
  refine ⟨?_, integrable_density_mul_of_norm_bdd hq hf hbound, ?_⟩
  · rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hq]
    exact hposv.sub_vectorMeasure hnegv
  · rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hq,
      VectorMeasure.integral_sub_vectorMeasure hposv hnegv,
      VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
      integral_withDensity_eq_integral_toReal_smul₀
        hq.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
      integral_withDensity_eq_integral_toReal_smul₀
        hqn.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [smul_eq_mul]
    rw [← integral_sub hpos hneg]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← sub_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    congr 1
    by_cases hx : 0 ≤ q x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · rw [max_eq_right (le_of_not_ge hx), max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
      ring

/-- Exact ordinary total variation of an integrable signed density. -/
theorem signedDensity_totalVariation {μ : Measure ℝ} {q : ℝ → ℝ}
    (hq : Integrable q μ) :
    (μ.withDensityᵥ q).variation.real univ = ∫ x, |q x| ∂μ := by
  rw [Measure.real, Measure.variation_withDensityᵥ hq,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← integral_norm_eq_lintegral_enorm hq.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]

/-- An integrable density over an atomless reference measure introduces no atoms. -/
@[simp] theorem signedDensity_singleton {μ : Measure ℝ} [NullSingletonClass μ] {q : ℝ → ℝ}
    (hq : Integrable q μ) (x : ℝ) : (μ.withDensityᵥ q) {x} = 0 := by
  rw [withDensityᵥ_apply hq (measurableSet_singleton x)]
  simp

end GapFamily.Analytic
