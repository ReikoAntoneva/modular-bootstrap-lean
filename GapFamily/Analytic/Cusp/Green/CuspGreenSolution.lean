import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionRepresentation
import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionDecay

/-!
# The actual scalar half-line Green solution

For a continuous compactly supported source, the kernel integral is ordinary,
has Dirichlet boundary value zero, and solves the forced scalar equation.
Positive real part of the spectral parameter gives outgoing decay.
-/

noncomputable section

namespace GapFamily.Analytic

open Filter MeasureTheory Set
open scoped Topology

/-- The actual integral is differentiable at every interior position. -/
theorem cuspGreenSolution_differentiableAt {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) {κ : ℂ} (hκ : κ ≠ 0)
    {t : ℝ} (ht : t₀ < t) :
    DifferentiableAt ℝ (cuspGreenSolution t₀ κ f) t := by
  obtain ⟨T, htT, hfT⟩ := exists_cuspSource_cutoff hfc t
  have heq : cuspGreenSolution t₀ κ f =ᶠ[𝓝 t] cuspGreenSolutionFormula t₀ T κ f := by
    filter_upwards [Ioo_mem_nhds ht htT] with v hv
    exact cuspGreenSolution_eq_formula t₀ T v hv.1.le hv.2.le hκ hf hfT
  exact ((hasDerivAt_cuspGreenSolutionFormula t₀ T hκ hf t).congr_of_eventuallyEq
    heq).differentiableAt

/-- The second derivative certificate belongs to the actual half-line integral. -/
theorem hasDerivAt_deriv_cuspGreenSolution {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) {κ : ℂ} (hκ : κ ≠ 0)
    {t : ℝ} (ht : t₀ < t) :
    HasDerivAt (deriv (cuspGreenSolution t₀ κ f))
      (κ ^ 2 * cuspGreenSolution t₀ κ f t - f t) t := by
  obtain ⟨T, htT, hfT⟩ := exists_cuspSource_cutoff hfc t
  have heq : cuspGreenSolution t₀ κ f =ᶠ[𝓝 t] cuspGreenSolutionFormula t₀ T κ f := by
    filter_upwards [Ioo_mem_nhds ht htT] with v hv
    exact cuspGreenSolution_eq_formula t₀ T v hv.1.le hv.2.le hκ hf hfT
  have hd := (hasDerivAt_deriv_cuspGreenSolutionFormula t₀ T hκ hf t).congr_of_eventuallyEq
    heq.deriv
  rwa [← cuspGreenSolution_eq_formula t₀ T t ht.le htT.le hκ hf hfT] at hd

/-- The genuine forced equation, with the derivative-jump source sign. -/
theorem cuspGreenSolution_forcedODE {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) {κ : ℂ} (hκ : κ ≠ 0)
    {t : ℝ} (ht : t₀ < t) :
    -deriv (deriv (cuspGreenSolution t₀ κ f)) t +
      κ ^ 2 * cuspGreenSolution t₀ κ f t = f t := by
  rw [(hasDerivAt_deriv_cuspGreenSolution hf hfc t₀ hκ ht).deriv]
  ring

/-- The actual solution has a continuous trace from the physical half-line. -/
theorem cuspGreenSolution_continuousWithinAt_boundary {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) {κ : ℂ} (hκ : κ ≠ 0) :
    ContinuousWithinAt (cuspGreenSolution t₀ κ f) (Ici t₀) t₀ := by
  obtain ⟨T, hT, hfT⟩ := exists_cuspSource_cutoff hfc t₀
  have heq : cuspGreenSolution t₀ κ f =ᶠ[𝓝[Ici t₀] t₀]
      cuspGreenSolutionFormula t₀ T κ f := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with v hv hvT
    exact cuspGreenSolution_eq_formula t₀ T v hv (le_of_lt hvT) hκ hf hfT
  exact (hasDerivAt_cuspGreenSolutionFormula t₀ T hκ hf t₀).continuousAt.continuousWithinAt
    |>.congr_of_eventuallyEq heq
      (cuspGreenSolution_eq_formula t₀ T t₀ le_rfl hT.le hκ hf hfT)

/-- The Dirichlet value is also the actual right-hand limit of the integral. -/
theorem cuspGreenSolution_tendsto_boundary {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) {κ : ℂ} (hκ : κ ≠ 0) :
    Tendsto (cuspGreenSolution t₀ κ f) (𝓝[>] t₀) (𝓝 0) := by
  have hc := (cuspGreenSolution_continuousWithinAt_boundary hf hfc t₀ hκ).mono
    Ioi_subset_Ici_self
  simpa only [ContinuousWithinAt, cuspGreenSolution_boundary] using hc

/-- A single endpoint collects convergence, boundary, forced equation and outgoing decay
for the actual integral, with no assumed differential equation or solution record. -/
theorem cuspGreenSolution_solves {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) {κ : ℂ} (hκ : 0 < κ.re) :
    (∀ t : ℝ, IntegrableOn (fun u : ℝ => cuspGreen t₀ t u κ * f u) (Ioi t₀)) ∧
      cuspGreenSolution t₀ κ f t₀ = 0 ∧
      Tendsto (cuspGreenSolution t₀ κ f) (𝓝[>] t₀) (𝓝 0) ∧
      (∀ t : ℝ, t₀ < t →
        DifferentiableAt ℝ (cuspGreenSolution t₀ κ f) t ∧
        HasDerivAt (deriv (cuspGreenSolution t₀ κ f))
          (κ ^ 2 * cuspGreenSolution t₀ κ f t - f t) t ∧
        -deriv (deriv (cuspGreenSolution t₀ κ f)) t +
          κ ^ 2 * cuspGreenSolution t₀ κ f t = f t) ∧
      Tendsto (cuspGreenSolution t₀ κ f) atTop (𝓝 0) := by
  have hk : κ ≠ 0 := by intro hz; simp [hz] at hκ
  refine ⟨fun t => cuspGreenSolution_integrableOn t₀ t κ hf hfc,
    cuspGreenSolution_boundary t₀ κ f, cuspGreenSolution_tendsto_boundary hf hfc t₀ hk,
    ?_, cuspGreenSolution_tendsto_zero hfc t₀ hκ⟩
  intro t ht
  exact ⟨cuspGreenSolution_differentiableAt hf hfc t₀ hk ht,
    hasDerivAt_deriv_cuspGreenSolution hf hfc t₀ hk ht,
    cuspGreenSolution_forcedODE hf hfc t₀ hk ht⟩

end GapFamily.Analytic
