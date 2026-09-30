import GapFamily.Analytic.Foundation.SignedDensityPairing
import Mathlib.Analysis.Complex.Basic

/-!
# Integration against an integrable signed density

The actual vector-measure integral against a real density agrees with its
ordinary Bochner integral. Integrability is with respect to the actual variation
measure; no boundedness or pointwise regularity of the test function is needed.
-/

open MeasureTheory Set

namespace GapFamily.Analytic

private theorem signedDensity_integral_data
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {q : α → ℝ} {f : α → E}
    (hq : Integrable q μ) (hf : (μ.withDensityᵥ q).Integrable f) :
    Integrable (fun x => q x • f x) μ ∧
      (∫ᵛ x, f x ∂<•μ.withDensityᵥ q) = ∫ x, q x • f x ∂μ := by
  have hqn : Integrable (fun x => -q x) μ := hq.neg
  have hf' : Integrable f (μ.withDensity (fun x => ‖q x‖ₑ)) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_withDensityᵥ hq] using hf
  have hposm : Integrable f (μ.withDensity (fun x => ENNReal.ofReal (q x))) :=
    hf'.mono_measure (withDensity_mono (Filter.Eventually.of_forall
      (fun x => Real.ofReal_le_enorm (q x))))
  have hnegm : Integrable f (μ.withDensity (fun x => ENNReal.ofReal (-q x))) := by
    apply hf'.mono_measure
    apply withDensity_mono
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [enorm_neg] using Real.ofReal_le_enorm (-q x))
  have hpos : Integrable (fun x => (ENNReal.ofReal (q x)).toReal • f x) μ :=
    (integrable_withDensity_iff_integrable_smul₀'
      hq.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hposm
  have hneg : Integrable (fun x => (ENNReal.ofReal (-q x)).toReal • f x) μ :=
    (integrable_withDensity_iff_integrable_smul₀'
      hqn.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hnegm
  have hsplit (x : α) :
      (ENNReal.ofReal (q x)).toReal • f x -
        (ENNReal.ofReal (-q x)).toReal • f x = q x • f x := by
    rw [← sub_smul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    congr 1
    by_cases hx : 0 ≤ q x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · rw [max_eq_right (le_of_not_ge hx), max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
      ring
  refine ⟨(hpos.sub hneg).congr (Filter.Eventually.of_forall hsplit), ?_⟩
  let : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (q x))) :=
    isFiniteMeasure_withDensity_ofReal hq.2
  let : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (-q x))) :=
    isFiniteMeasure_withDensity_ofReal hq.neg.2
  have hposv : (μ.withDensity (fun x => ENNReal.ofReal (q x))).toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hposm
  have hnegv : (μ.withDensity (fun x => ENNReal.ofReal (-q x))).toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hnegm
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hq,
    VectorMeasure.integral_sub_vectorMeasure hposv hnegv,
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      hq.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul₀
      hqn.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    ← integral_sub hpos hneg]
  exact integral_congr_ae (Filter.Eventually.of_forall hsplit)

/-- Actual variation integrability implies ordinary integrability after
multiplying the test function by the signed density. -/
theorem signedDensity_integrable_smul
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {q : α → ℝ} {f : α → E}
    (hq : Integrable q μ) (hf : (μ.withDensityᵥ q).Integrable f) :
    Integrable (fun x => q x • f x) μ :=
  (signedDensity_integral_data hq hf).1

/-- The signed integral against an integrable real density is its ordinary
density-weighted Bochner integral. -/
theorem signedDensity_integral_eq_integral_smul
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {q : α → ℝ} {f : α → E}
    (hq : Integrable q μ) (hf : (μ.withDensityᵥ q).Integrable f) :
    (∫ᵛ x, f x ∂<•μ.withDensityᵥ q) = ∫ x, q x • f x ∂μ :=
  (signedDensity_integral_data hq hf).2

/-- Complex kernels may be paired directly with an ordinary real signed
density; both sides are genuine integrals. -/
theorem signedDensity_integral_eq_integral_mul
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : α → ℝ} {f : α → ℂ}
    (hq : Integrable q μ) (hf : (μ.withDensityᵥ q).Integrable f) :
    (∫ᵛ x, f x ∂<•μ.withDensityᵥ q) = ∫ x, f x * (q x : ℂ) ∂μ := by
  simpa only [Complex.real_smul, mul_comm] using
    signedDensity_integral_eq_integral_smul hq hf

end GapFamily.Analytic
