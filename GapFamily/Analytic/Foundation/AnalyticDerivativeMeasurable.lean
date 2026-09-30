import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

noncomputable section
namespace GapFamily.Analytic.DominatedAnalytic
open Set Filter MeasureTheory
open scoped Topology

/-- Parameterwise measurable analytic slices have measurable actual derivatives
at each interior parameter. No joint measurability hypothesis is needed. -/
theorem aestronglyMeasurable_deriv_of_analyticOnNhd
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {μ : Measure α}
    {F : ℂ → α → E} {c z₀ : ℂ} {r : ℝ}
    (hz₀ : z₀ ∈ Metric.ball c r)
    (hmeas : ∀ z ∈ Metric.ball c r, AEStronglyMeasurable (F z) μ)
    (hana : ∀ᵐ a ∂μ, AnalyticOnNhd ℂ (fun z => F z a) (Metric.ball c r)) :
    AEStronglyMeasurable (fun a => deriv (fun z => F z a) z₀) μ := by
  classical
  let q (z : ℂ) (a : α) : E :=
    if z ∈ Metric.ball c r then (z - z₀)⁻¹ • (F z a - F z₀ a) else 0
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] z₀) (f := q)
  · intro z
    by_cases hz : z ∈ Metric.ball c r
    · simpa only [q, hz, ite_true, Pi.smul_apply, Pi.sub_apply] using
        ((hmeas z hz).fun_sub (hmeas z₀ hz₀)).fun_const_smul ((z - z₀)⁻¹)
    · simpa only [q, hz, ite_false] using (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : α => (0 : E)) μ)
  · filter_upwards [hana] with a ha
    have hd := ((ha z₀ hz₀).differentiableAt.hasDerivAt).tendsto_slope
    apply hd.congr'
    have hball : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Metric.ball c r :=
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hz₀)
    filter_upwards [hball] with z hz
    simp only [q, hz, ite_true, slope_def_module]

end GapFamily.Analytic.DominatedAnalytic
