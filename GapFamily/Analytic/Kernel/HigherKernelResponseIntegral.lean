import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Schwarz

/-!
# Entire parameter integral with local ordinary domination

The derivative integrals below are proved integrable. Slice measurability
is propagated to the derivative by the punctured difference-quotient limit.
-/

noncomputable section
open MeasureTheory Filter Metric
open scoped Topology
namespace GapFamily.Analytic

theorem aestronglyMeasurable_deriv_parameter
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℂ → α → ℂ} {z0 : ℂ}
    (hm : ∀ z, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ a ∂μ, DifferentiableAt ℂ (fun z => F z a) z0) :
    AEStronglyMeasurable (fun a => deriv (fun z => F z a) z0) μ := by
  refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ))
    (f := fun t a => t⁻¹ • (F (z0 + t) a - F z0 a)) ?_ ?_
  · intro t
    exact ((hm _).sub (hm _)).const_smul (t⁻¹ : ℂ)
  · filter_upwards [hd] with a ha
    exact ha.hasDerivAt.tendsto_slope_zero

theorem integrable_of_entire_disk_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : ℂ → α → ℂ}
    (hmeas : ∀ z, AEStronglyMeasurable (F z) μ)
    (hbound : ∀ z₀, ∃ b : α → ℝ, Integrable b μ ∧
      ∀ᵐ a ∂μ, ∀ z ∈ closedBall z₀ 2, ‖F z a‖ ≤ b a)
    (z : ℂ) : Integrable (F z) μ := by
  obtain ⟨b, hb, hbound⟩ := hbound z
  exact hb.mono' (hmeas z)
    (hbound.mono fun a ha => ha z (mem_closedBall_self (by norm_num)))

theorem hasDerivAt_integral_of_entire_disk_bound {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {F : ℂ → α → ℂ}
    (hmeas : ∀ z, AEStronglyMeasurable (F z) μ)
    (hdiff : ∀ᵐ a ∂μ, Differentiable ℂ (fun z => F z a))
    (hbound : ∀ z₀, ∃ b : α → ℝ, Integrable b μ ∧
      ∀ᵐ a ∂μ, ∀ z ∈ closedBall z₀ 2, ‖F z a‖ ≤ b a) (z₀ : ℂ) :
    Integrable (fun a => deriv (fun z => F z a) z₀) μ ∧
      HasDerivAt (fun z => ∫ a, F z a ∂μ)
        (∫ a, deriv (fun z => F z a) z₀ ∂μ) z₀ := by
  obtain ⟨b, hb, hba⟩ := hbound z₀
  have hdb : ∀ᵐ a ∂μ, ∀ z ∈ ball z₀ 1,
      ‖deriv (fun w => F w a) z‖ ≤ 2 * b a := by
    filter_upwards [hdiff, hba] with a ha hba
    intro z hz
    have hzo : z ∈ closedBall z₀ 2 := by
      exact le_trans (Metric.mem_ball.mp hz).le (by norm_num)
    have hm : Set.MapsTo (fun w => F w a) (ball z 1)
        (closedBall (F z a) (2 * b a)) := by
      intro w hw
      have hwo : w ∈ closedBall z₀ 2 := by
        calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
          _ ≤ 1 + 1 := add_le_add (Metric.mem_ball.mp hw).le (Metric.mem_ball.mp hz).le
          _ = 2 := by norm_num
      rw [mem_closedBall, dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hba w hwo, hba z hzo])
    simpa using Complex.norm_deriv_le_div_of_mapsTo_ball
      ha.differentiableOn hm (by norm_num : (0 : ℝ) < 1)
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall hmeas)
    (integrable_of_entire_disk_bound hmeas hbound z₀)
    (aestronglyMeasurable_deriv_parameter hmeas (hdiff.mono fun a ha => ha z₀))
    hdb (hb.const_mul 2) (hdiff.mono fun a ha z _ => (ha z).hasDerivAt)

theorem differentiable_integral_of_entire_disk_bound {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {F : ℂ → α → ℂ}
    (hmeas : ∀ z, AEStronglyMeasurable (F z) μ)
    (hdiff : ∀ᵐ a ∂μ, Differentiable ℂ (fun z => F z a))
    (hbound : ∀ z₀, ∃ b : α → ℝ, Integrable b μ ∧
      ∀ᵐ a ∂μ, ∀ z ∈ closedBall z₀ 2, ‖F z a‖ ≤ b a) :
    Differentiable ℂ (fun z => ∫ a, F z a ∂μ) :=
  fun z => (hasDerivAt_integral_of_entire_disk_bound hmeas hdiff hbound z).2.differentiableAt

end GapFamily.Analytic
