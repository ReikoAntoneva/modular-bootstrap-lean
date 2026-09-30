import GapFamily.Analytic.Elliptic.L2DominatedDerivative
import GapFamily.Analytic.Foundation.AnalyticDerivativeMeasurable
import Mathlib.Analysis.Complex.Liouville

noncomputable section
namespace GapFamily.Analytic.DominatedAnalytic
open Set Filter MeasureTheory Metric
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Entire scalar slices with a common local square-integrable majorant define an entire
L2-valued function. Derivative measurability and domination follow from the original slices;
neither is an additional hypothesis. -/
theorem differentiable_L2_of_entire_dominated
    {u : ℂ → Lp ℂ 2 μ} {F : ℂ → X → ℂ}
    (hrep : ∀ z, u z =ᵐ[μ] F z)
    (hentire : ∀ᵐ x ∂μ, Differentiable ℂ (fun z => F z x))
    (hbound : ∀ z₀, ∃ B : X → ℝ, MemLp B 2 μ ∧
      ∀ᵐ x ∂μ, ∀ z ∈ closedBall z₀ 2, ‖F z x‖ ≤ B x) :
    Differentiable ℂ u := by
  intro z₀
  obtain ⟨B, hB, hb⟩ := hbound z₀
  let F' : ℂ → X → ℂ := fun z x => deriv (fun w => F w x) z
  have hmeas (z : ℂ) : AEStronglyMeasurable (F z) μ :=
    (Lp.aestronglyMeasurable (u z)).congr (hrep z)
  have hderiv : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ 1,
      HasDerivAt (fun w => F w x) (F' z x) z := by
    filter_upwards [hentire] with x hx
    exact fun z _ => (hx z).hasDerivAt
  have hderiv_bound : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ 1, ‖F' z x‖ ≤ B x := by
    filter_upwards [hentire, hb] with x hx hbx
    intro z hz
    have hC (w : ℂ) (hw : w ∈ sphere z 1) : ‖F w x‖ ≤ B x := by
      apply hbx w
      apply mem_closedBall.mpr
      calc
        dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ 2 := by
          have hw' := mem_sphere.mp hw
          have hz' := mem_ball.mp hz
          linarith
    simpa only [F', div_one] using
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
        (by norm_num : (0 : ℝ) < 1) hx.diffContOnCl hC
  have hF'meas : AEStronglyMeasurable (F' z₀) μ := by
    apply aestronglyMeasurable_deriv_of_analyticOnNhd
      (c := z₀) (r := 1) (mem_ball_self (by norm_num)) (fun z _ => hmeas z)
    filter_upwards [hentire] with x hx
    exact fun z _ => hx.analyticAt z
  have hF' : MemLp (F' z₀) 2 μ :=
    hB.mono' hF'meas (hderiv_bound.mono fun x hx => hx z₀ (mem_ball_self (by norm_num)))
  exact (DominatedL2.hasDerivAt_L2_of_dominated_deriv
    (by norm_num : (0 : ℝ) < 1) (fun z _ => hrep z) hderiv hderiv_bound hB hF').differentiableAt

end GapFamily.Analytic.DominatedAnalytic
