import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionAnalyticBound
import GapFamily.Analytic.Kernel.HigherKernelResponseIntegral

/-! Entire dependence of the actual compact-source scalar Green response.
The proof uses its ordinary integral and a proved local integrable majorant. -/

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Filter Set Metric
open scoped Topology

/-- Compact support supplies an ordinary dominating function on each parameter disk. -/
theorem cuspGreenSolution_disk_domination (t₀ t : ℝ) (ht : t₀ ≤ t)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (κ₀ : ℂ) :
    ∃ b : ℝ → ℝ, Integrable b (volume.restrict (Ioi t₀)) ∧
      ∀ᵐ u : ℝ ∂volume.restrict (Ioi t₀),
        ∀ κ ∈ closedBall κ₀ 2, ‖cuspGreen t₀ t u κ * f u‖ ≤ b u := by
  obtain ⟨U, _, hfU⟩ := exists_cuspSource_cutoff hfc t₀
  refine ⟨fun u => ((t - t₀) * Real.exp ((‖κ₀‖ + 2) * (t + U - 2 * t₀))) * ‖f u‖,
    (((hf.integrable_of_hasCompactSupport hfc).norm.integrableOn).const_mul _), ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  intro κ hκ
  have hκR : ‖κ‖ ≤ ‖κ₀‖ + 2 := norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hκ)
  by_cases huU : u ≤ U
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_cuspGreen_on_collar_le t₀ t U (‖κ₀‖ + 2) t u κ ht le_rfl hu.le huU hκR)
      (norm_nonneg _)
  · simp [hfU u (lt_of_not_ge huU)]

/-- The genuine Green response is entire through κ = 0 for every physical position. -/
theorem differentiable_cuspGreenSolution_parameter (t₀ t : ℝ) (ht : t₀ ≤ t)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Differentiable ℂ (fun κ => cuspGreenSolution t₀ κ f t) := by
  apply differentiable_integral_of_entire_disk_bound
    (fun κ => ((cuspGreen_continuous_source t₀ t κ).mul hf).aestronglyMeasurable) _
    (cuspGreenSolution_disk_domination t₀ t ht hf hfc)
  exact Eventually.of_forall fun u => (cuspGreen_differentiable t₀ t u).mul_const (f u)

/-- Parameter differentiation commutes with the ordinary source integral;
the derivative integrand is itself proved integrable. -/
theorem hasDerivAt_cuspGreenSolution_parameter (t₀ t : ℝ) (ht : t₀ ≤ t)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (κ : ℂ) :
    Integrable (fun u : ℝ => deriv (fun z : ℂ => cuspGreen t₀ t u z * f u) κ)
      (volume.restrict (Ioi t₀)) ∧
      HasDerivAt (fun z : ℂ => cuspGreenSolution t₀ z f t)
        (∫ u : ℝ in Ioi t₀, deriv (fun z : ℂ => cuspGreen t₀ t u z * f u) κ) κ := by
  exact hasDerivAt_integral_of_entire_disk_bound
    (fun z => ((cuspGreen_continuous_source t₀ t z).mul hf).aestronglyMeasurable)
    (Eventually.of_forall fun u => (cuspGreen_differentiable t₀ t u).mul_const (f u))
    (cuspGreenSolution_disk_domination t₀ t ht hf hfc) κ

/-- Holomorphy is asserted for the actual source integral, including its threshold value. -/
theorem analyticAt_cuspGreenSolution_parameter (t₀ t : ℝ) (ht : t₀ ≤ t)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (κ : ℂ) :
    AnalyticAt ℂ (fun z => cuspGreenSolution t₀ z f t) κ :=
  (differentiable_cuspGreenSolution_parameter t₀ t ht hf hfc).analyticAt κ

/-- The threshold value of the continued response is the actual min-kernel integral. -/
@[simp] theorem cuspGreenSolution_zero (t₀ t : ℝ) (f : ℝ → ℂ) :
    cuspGreenSolution t₀ 0 f t =
      ∫ u : ℝ in Ioi t₀, ((min t u - t₀ : ℝ) : ℂ) * f u := by
  simp only [cuspGreenSolution, cuspGreen_zero]

/-- In particular the actual entire response converges to its removable threshold integral. -/
theorem cuspGreenSolution_tendsto_parameter_zero (t₀ t : ℝ) (ht : t₀ ≤ t)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun κ => cuspGreenSolution t₀ κ f t) (𝓝 (0 : ℂ))
      (𝓝 (∫ u : ℝ in Ioi t₀, ((min t u - t₀ : ℝ) : ℂ) * f u)) := by
  simpa only [cuspGreenSolution_zero] using
    (differentiable_cuspGreenSolution_parameter t₀ t ht hf hfc).continuous.tendsto 0

end GapFamily.Analytic
