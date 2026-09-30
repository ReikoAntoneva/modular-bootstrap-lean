import GapFamily.Analytic.Foundation.AnalyticDerivativeMeasurable
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Bochner analyticity from actual measurable slices and a uniform integrable majorant. -/
noncomputable section
namespace GapFamily.Analytic.DominatedAnalytic
open Set Filter MeasureTheory Metric
open scoped Topology

variable {α B : Type*} [MeasurableSpace α]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedSpace ℂ B] [CompleteSpace B]

omit [NormedSpace ℝ B] [CompleteSpace B] in
private theorem norm_deriv_le_of_analytic_ball {f : ℂ → B} {z₀ z : ℂ} {r C : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (ball z₀ r))
    (hbound : ∀ w ∈ ball z₀ r, ‖f w‖ ≤ C) (hz : z ∈ ball z₀ (3 * r / 4)) :
    ‖deriv f z‖ ≤ C / (r / 4) := by
  have hclosed : closedBall z (r / 4) ⊆ ball z₀ r := by
    intro w hw
    have hw' := mem_closedBall.mp hw
    have hz' := mem_ball.mp hz
    change dist w z₀ < r
    calc
      dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < r / 4 + 3 * r / 4 := add_lt_add_of_le_of_lt hw' hz'
      _ = r := by ring
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
    (hf.differentiableOn.diffContOnCl_ball hclosed)
  intro w hw
  exact hbound w (hclosed (sphere_subset_closedBall hw))

/-- Uniform domination on an actual complex ball makes its Bochner integral
analytic at the center. Derivative domination and measurability are consequences
of the stated hypotheses, rather than additional assumptions. -/
theorem analyticAt_integral_of_dominated
    {μ : Measure α} {F : ℂ → α → B} {z₀ : ℂ} {r : ℝ} {bound : α → ℝ}
    (hr : 0 < r)
    (hmeas : ∀ z ∈ ball z₀ r, AEStronglyMeasurable (F z) μ)
    (hanalytic : ∀ᵐ a ∂μ, AnalyticOnNhd ℂ (fun z => F z a) (ball z₀ r))
    (hbound : ∀ᵐ a ∂μ, ∀ z ∈ ball z₀ r, ‖F z a‖ ≤ bound a)
    (hint : Integrable bound μ) :
    AnalyticAt ℂ (fun z => ∫ a, F z a ∂μ) z₀ := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [ball_mem_nhds z₀ (show 0 < r / 2 by positivity)] with z hz
  have hzfull : z ∈ ball z₀ r := ball_subset_ball (by linarith) hz
  have hzthree : z ∈ ball z₀ (3 * r / 4) := ball_subset_ball (by linarith) hz
  have hmeas_z : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) μ := by
    filter_upwards [isOpen_ball.mem_nhds hzfull] with w hw
    exact hmeas w hw
  have hint_z : Integrable (F z) μ := hint.mono' (hmeas z hzfull)
    (hbound.mono (fun a ha => ha z hzfull))
  have hderiv_meas : AEStronglyMeasurable (fun a => deriv (fun w => F w a) z) μ :=
    aestronglyMeasurable_deriv_of_analyticOnNhd hzfull hmeas hanalytic
  have hderiv_bound : ∀ᵐ a ∂μ, ∀ w ∈ ball z₀ (3 * r / 4),
      ‖deriv (fun v => F v a) w‖ ≤ bound a / (r / 4) := by
    filter_upwards [hanalytic, hbound] with a ha hb
    intro w hw
    exact norm_deriv_le_of_analytic_ball hr ha hb hw
  have hderiv : ∀ᵐ a ∂μ, ∀ w ∈ ball z₀ (3 * r / 4),
      HasDerivAt (fun v => F v a) (deriv (fun v => F v a) w) w := by
    filter_upwards [hanalytic] with a ha
    intro w hw
    exact (ha w (ball_subset_ball (by linarith) hw)).differentiableAt.hasDerivAt
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (isOpen_ball.mem_nhds hzthree) hmeas_z hint_z hderiv_meas hderiv_bound
    (hint.div_const (r / 4)) hderiv).2.differentiableAt

end GapFamily.Analytic.DominatedAnalytic
