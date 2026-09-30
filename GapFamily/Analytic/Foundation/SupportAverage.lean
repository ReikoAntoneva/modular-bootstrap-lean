import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section

namespace GapFamily.Analytic.SupportAverage

open MeasureTheory Set Filter
open scoped Topology

variable {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ]

/-- A normalized Bochner integral stays within the pointwise error bound.
The positive finite mass and genuine integrability are explicit. -/
theorem norm_setAverage_sub_le {S : Set X} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    {f : X → E} (hf : IntegrableOn f S μ) (c : E) {ε : ℝ}
    (hbound : ∀ x ∈ S, ‖f x - c‖ ≤ ε) :
    ‖(⨍ x in S, f x ∂μ) - c‖ ≤ ε := by
  have hmass : 0 < μ.real S := ENNReal.toReal_pos hS0 (measure_ne_top μ S)
  have hc : IntegrableOn (fun _ : X => c) S μ := integrable_const _
  have he : (⨍ x in S, f x ∂μ) - c = ⨍ x in S, (f x - c) ∂μ := by
    rw [average_fun_sub hf hc, setAverage_const hS0 (measure_ne_top μ S)]
  rw [he, setAverage_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hmass.le)]
  have hb : ‖∫ x in S, f x - c ∂μ‖ ≤ ε * μ.real S := by
    simpa only [measureReal_restrict_apply_univ] using
      (norm_integral_le_of_norm_le_const
        ((ae_restrict_iff' hS).mpr (Filter.Eventually.of_forall hbound)))
  calc
    _ ≤ (μ.real S)⁻¹ * (ε * μ.real S) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hmass.le)
    _ = ε := by field_simp

/-- A continuous Banach-valued source is recovered by normalized shrinking-ball
integrals at a measure-support point. Only integrability on one neighborhood
is required; integrability on the whole source space is unnecessary. -/
theorem tendsto_setAverage_ball [MetricSpace X] [BorelSpace X]
    {f : X → E} {x : X} {R : ℝ} (hR : 0 < R)
    (hf : IntegrableOn f (Metric.ball x R) μ) (hc : ContinuousAt f x)
    (hx : x ∈ μ.support) :
    Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, f y ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (by linarith)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with r hr hrd hrR
  have hr0 : 0 < r := hr
  have hm : μ (Metric.ball x r) ≠ 0 :=
    ((Measure.mem_support_iff_forall x).mp hx _ (Metric.ball_mem_nhds x hr0)).ne'
  have hfr : IntegrableOn f (Metric.ball x r) μ :=
    hf.mono_set (Metric.ball_subset_ball hrR.le)
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (norm_setAverage_sub_le μ Metric.isOpen_ball.measurableSet hm
    hfr (f x) (fun y hy => ?_)) (show ε / 2 < ε by linarith)
  exact (show ‖f y - f x‖ < ε / 2 by
    simpa only [dist_eq_norm] using hd (Metric.mem_ball.mp hy |>.trans hrd)).le

/-- Convenient global-integrability specialization. -/
theorem tendsto_setAverage_ball_of_integrable [MetricSpace X] [BorelSpace X]
    {f : X → E} (hf : Integrable f μ) {x : X} (hc : ContinuousAt f x)
    (hx : x ∈ μ.support) :
    Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, f y ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) :=
  tendsto_setAverage_ball μ zero_lt_one hf.integrableOn hc hx

end GapFamily.Analytic.SupportAverage
