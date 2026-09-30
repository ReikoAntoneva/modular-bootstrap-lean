import GapFamily.Analytic.Foundation.SupportAverage

noncomputable section

namespace GapFamily.Analytic.SupportAverage

open MeasureTheory Set Filter
open scoped Topology

variable {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ]

/-- A uniform pointwise error bounds the difference of genuine normalized
Bochner integrals on a measurable set of positive finite mass. -/
theorem norm_setAverage_sub_setAverage_le {S : Set X}
    (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    {f g : X → E} (hf : IntegrableOn f S μ) (hg : IntegrableOn g S μ)
    {ε : ℝ} (hbound : ∀ x ∈ S, ‖f x - g x‖ ≤ ε) :
    ‖(⨍ x in S, f x ∂μ) - (⨍ x in S, g x ∂μ)‖ ≤ ε := by
  have h := norm_setAverage_sub_le μ hS hS0 (hf.sub hg) (0 : E)
    (fun x hx => by simpa only [sub_zero, Pi.sub_apply] using hbound x hx)
  simpa only [Pi.sub_apply, average_fun_sub hf hg, sub_zero] using h

/-- If the sources converge uniformly on the very balls being averaged,
their shrinking-ball averages recover the limiting source at a support point.
Both source integrability and the vanishing uniform error are explicit. -/
theorem tendsto_setAverage_ball_of_uniform [MetricSpace X] [BorelSpace X]
    {F : ℝ → X → E} {f : X → E} {x : X} {R : ℝ} (hR : 0 < R)
    (hf : IntegrableOn f (Metric.ball x R) μ) (hc : ContinuousAt f x)
    (hx : x ∈ μ.support)
    (hF : ∀ r : ℝ, 0 < r → r < R → IntegrableOn (F r) (Metric.ball x r) μ)
    {error : ℝ → ℝ}
    (hbound : ∀ r : ℝ, 0 < r → r < R →
      ∀ y ∈ Metric.ball x r, ‖F r y - f y‖ ≤ error r)
    (herror : Tendsto error (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, F r y ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have hbase := tendsto_setAverage_ball μ hR hf hc hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hεhalf : 0 < ε / 2 := by linarith
  have hbaseε := Metric.tendsto_nhds.mp hbase (ε / 2) hεhalf
  have herrorε := (tendsto_order.mp herror).2 (ε / 2) hεhalf
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds,
    hbaseε, herrorε] with r hr hrR hb he
  have hr0 : 0 < r := hr
  have hm : μ (Metric.ball x r) ≠ 0 :=
    ((Measure.mem_support_iff_forall x).mp hx _ (Metric.ball_mem_nhds x hr0)).ne'
  have hfr : IntegrableOn f (Metric.ball x r) μ :=
    hf.mono_set (Metric.ball_subset_ball hrR.le)
  have hdiff : dist (⨍ y in Metric.ball x r, F r y ∂μ)
      (⨍ y in Metric.ball x r, f y ∂μ) ≤ error r := by
    rw [dist_eq_norm]
    exact norm_setAverage_sub_setAverage_le μ Metric.isOpen_ball.measurableSet hm
      (hF r hr0 hrR) hfr (hbound r hr0 hrR)
  calc
    _ ≤ dist (⨍ y in Metric.ball x r, F r y ∂μ)
          (⨍ y in Metric.ball x r, f y ∂μ) +
        dist (⨍ y in Metric.ball x r, f y ∂μ) (f x) := dist_triangle _ _ _
    _ ≤ error r + dist (⨍ y in Metric.ball x r, f y ∂μ) (f x) :=
      add_le_add hdiff le_rfl
    _ < ε := by linarith

end GapFamily.Analytic.SupportAverage
