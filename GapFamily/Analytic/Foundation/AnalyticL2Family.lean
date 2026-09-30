import GapFamily.Analytic.Elliptic.L2DominatedDerivative
import GapFamily.Analytic.Foundation.AnalyticDerivativeMeasurable
import Mathlib.Analysis.Complex.Liouville

noncomputable section
namespace GapFamily.Analytic.DominatedL2
open Set Filter MeasureTheory Metric
open scoped Topology
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A scalar Cauchy estimate on a smaller ball supplies the derivative majorant. -/
theorem norm_deriv_le_of_analytic_ball {f : ℂ → ℂ} {c z : ℂ} {r C : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (ball c r))
    (hb : ∀ w ∈ ball c r, ‖f w‖ ≤ C) (hz : z ∈ ball c (r / 2)) :
    ‖deriv f z‖ ≤ C / (r / 2) := by
  have hsub : closedBall z (r / 2) ⊆ ball c r := by
    intro w hw
    have hw' := mem_closedBall.mp hw
    have hz' := mem_ball.mp hz
    change dist w c < r
    calc
      dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add_of_le_of_lt hw' hz'
      _ = r := by ring
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hr)
    (hf.differentiableOn.diffContOnCl_ball hsub)
  intro w hw
  exact hb w (hsub (sphere_subset_closedBall hw))

/-- Pointwise analyticity and a local common L2 majorant imply genuine L2 differentiability.
The derivative's measurability and L2 membership are derived, not assumed. -/
theorem differentiableAt_L2_of_dominated
    {u : ℂ → Lp ℂ 2 μ} {F : ℂ → X → ℂ} {z₀ : ℂ} {r : ℝ} {B : X → ℝ}
    (hr : 0 < r)
    (hrep : ∀ z ∈ ball z₀ r, u z =ᵐ[μ] F z)
    (hanalytic : ∀ᵐ x ∂μ, AnalyticOnNhd ℂ (fun z => F z x) (ball z₀ r))
    (hbound : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ r, ‖F z x‖ ≤ B x)
    (hB : MemLp B 2 μ) : DifferentiableAt ℂ u z₀ := by
  have hm (z : ℂ) (hz : z ∈ ball z₀ r) : AEStronglyMeasurable (F z) μ :=
    (Lp.aestronglyMeasurable (u z)).congr (hrep z hz)
  have hdm : AEStronglyMeasurable (fun x => deriv (fun z => F z x) z₀) μ :=
    DominatedAnalytic.aestronglyMeasurable_deriv_of_analyticOnNhd
      (mem_ball_self hr) hm hanalytic
  have hdb : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ (r / 2),
      ‖deriv (fun w => F w x) z‖ ≤ B x / (r / 2) := by
    filter_upwards [hanalytic, hbound] with x ha hb
    intro z hz
    exact norm_deriv_le_of_analytic_ball hr ha hb hz
  have hBderiv : MemLp (fun x => B x / (r / 2)) 2 μ := by
    simpa only [div_eq_mul_inv, mul_comm] using hB.const_mul ((r / 2)⁻¹)
  have hdLp : MemLp (fun x => deriv (fun z => F z x) z₀) 2 μ :=
    hBderiv.mono' hdm
      (hdb.mono (fun x hx => hx z₀ (mem_ball_self (half_pos hr))))
  have hdd : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ (r / 2),
      HasDerivAt (fun w => F w x) (deriv (fun w => F w x) z) z := by
    filter_upwards [hanalytic] with x hx
    intro z hz
    exact (hx z (ball_subset_ball (by linarith) hz)).differentiableAt.hasDerivAt
  exact (hasDerivAt_L2_of_dominated_deriv (u := u) (F := F)
    (F' := fun z x => deriv (fun w => F w x) z) (half_pos hr)
    (fun z hz => hrep z (ball_subset_ball (by linarith) hz))
    hdd hdb hBderiv hdLp).differentiableAt

/-- Norm analyticity of an actual L2 family from its measurable analytic representatives
and a locally common L2 majorant. No finite-measure or supplied norm-holomorphy premise is used. -/
theorem analyticAt_L2_of_dominated
    {u : ℂ → Lp ℂ 2 μ} {F : ℂ → X → ℂ} {z₀ : ℂ} {r : ℝ} {B : X → ℝ}
    (hr : 0 < r)
    (hrep : ∀ z ∈ ball z₀ r, u z =ᵐ[μ] F z)
    (hanalytic : ∀ᵐ x ∂μ, AnalyticOnNhd ℂ (fun z => F z x) (ball z₀ r))
    (hbound : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ r, ‖F z x‖ ≤ B x)
    (hB : MemLp B 2 μ) : AnalyticAt ℂ u z₀ := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [ball_mem_nhds z₀ (half_pos hr)] with z hz
  have hsub : ball z (r / 2) ⊆ ball z₀ r := by
    intro w hw
    have hw' := mem_ball.mp hw
    have hz' := mem_ball.mp hz
    change dist w z₀ < r
    calc
      dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hw' hz'
      _ = r := by ring
  exact differentiableAt_L2_of_dominated (half_pos hr)
    (fun w hw => hrep w (hsub hw))
    (hanalytic.mono (fun x hx => hx.mono hsub))
    (hbound.mono (fun x hx w hw => hx w (hsub hw))) hB

end GapFamily.Analytic.DominatedL2
