import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory
open scoped Topology

/-- Uniform convergence on the support of a continuous compact test permits
passing the actual test pairing through the limit. All integrability follows
from the compact support and the locally finite measure hypothesis. -/
theorem tendsto_integral_compactTest_of_tendstoUniformlyOn
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → ℂ} {f a : α → ℂ}
    (hF : ∀ i, Continuous (F i)) (hf : Continuous f) (ha : Continuous a)
    (hca : HasCompactSupport a)
    (hlim : TendstoUniformlyOn F f l (tsupport a)) :
    Tendsto (fun i => ∫ x, a x * F i x ∂μ) l (𝓝 (∫ x, a x * f x ∂μ)) := by
  let bound : α → ℝ := fun x => ‖a x‖ * (‖f x‖ + 1)
  have hbcont : Continuous bound := ha.norm.mul (hf.norm.add continuous_const)
  have hbcompact : HasCompactSupport bound := hca.norm.mul_right
  have hbint : Integrable bound μ := hbcont.integrable_of_hasCompactSupport hbcompact
  have hnear := Metric.tendstoUniformlyOn_iff.mp hlim 1 zero_lt_one
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Eventually.of_forall fun i =>
      ((ha.mul (hF i)).integrable_of_hasCompactSupport hca.mul_right).aestronglyMeasurable
  · filter_upwards [hnear] with i hi
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport a
    · have hb : ‖F i x‖ ≤ ‖f x‖ + 1 :=
        norm_le_norm_add_const_of_dist_le (by simpa only [dist_comm] using (hi x hx).le)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    · simp [bound, image_eq_zero_of_notMem_tsupport hx]
  · exact hbint
  · apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport a
    · exact (hlim.tendsto_at hx).const_mul (a x)
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
      exact tendsto_const_nhds

end GapFamily.Analytic.SpatialPoint
