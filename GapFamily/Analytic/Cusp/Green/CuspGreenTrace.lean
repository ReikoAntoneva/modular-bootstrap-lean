import GapFamily.Analytic.Cusp.Green.CuspGreenThreshold
import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionAnalytic

/-! The actual scalar Dirichlet solution has a proved one-sided derivative trace. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Filter Set Metric
open scoped Topology

/-- The derivative in the direction of increasing cusp height at the boundary. -/
def cuspGreenBoundaryTrace (t₀ : ℝ) (κ : ℂ) (f : ℝ → ℂ) : ℂ :=
  ∫ u : ℝ in Ioi t₀, Complex.exp (-κ * ((u - t₀ : ℝ) : ℂ)) * f u

/-- The boundary trace is an ordinary convergent source integral. -/
theorem cuspGreenBoundaryTrace_integrable (t₀ : ℝ) (κ : ℂ) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun u : ℝ => Complex.exp (-κ * ((u - t₀ : ℝ) : ℂ)) * f u) := by
  apply Continuous.integrable_of_hasCompactSupport _ hfc.mul_left
  fun_prop

@[simp] theorem cuspGreenBoundaryTrace_zero (t₀ : ℝ) (f : ℝ → ℂ) :
    cuspGreenBoundaryTrace t₀ 0 f = ∫ u : ℝ in Ioi t₀, f u := by
  simp [cuspGreenBoundaryTrace]

/-- A genuine support cutoff changes the half-line trace into a finite integral. -/
theorem cuspGreenBoundaryTrace_eq_interval (t₀ T : ℝ) (hT : t₀ ≤ T)
    (κ : ℂ) {f : ℝ → ℂ} (hfT : ∀ u : ℝ, T < u → f u = 0) :
    cuspGreenBoundaryTrace t₀ κ f =
      ∫ u : ℝ in t₀..T, Complex.exp (-κ * ((u - t₀ : ℝ) : ℂ)) * f u := by
  rw [intervalIntegral.integral_of_le hT]
  unfold cuspGreenBoundaryTrace
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc t₀ T ⊆ Ioi t₀ from fun _ hu => hu.1)
  intro u hu
  have huT : T < u := by
    have hn : ¬(t₀ < u ∧ u ≤ T) := hu.2
    exact lt_of_not_ge (fun h => hn ⟨hu.1, h⟩)
  rw [hfT u huT, mul_zero]

/-- The derivative of the actual finite Green formula has exactly the trace value. -/
theorem cuspGreenSolutionFormulaDeriv_boundary (t₀ T : ℝ) (hT : t₀ ≤ T)
    (κ : ℂ) {f : ℝ → ℂ} (hfT : ∀ u : ℝ, T < u → f u = 0) :
    cuspGreenSolutionFormulaDeriv t₀ T κ f t₀ = cuspGreenBoundaryTrace t₀ κ f := by
  rw [cuspGreenBoundaryTrace_eq_interval t₀ T hT κ hfT]
  unfold cuspGreenSolutionFormulaDeriv
  simp only [intervalIntegral.integral_same, mul_zero, zero_add]
  rw [show -κ * ((t₀ : ℂ) - 2 * t₀) = κ * t₀ by ring]
  calc
    _ = Complex.exp (κ * t₀) * ∫ u : ℝ in t₀..T, Complex.exp (-κ * u) * f u := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      rw [← mul_assoc, ← Complex.exp_add]
      push_cast
      congr 2
      ring

/-- The finite threshold derivative gives the same ordinary boundary trace. -/
theorem cuspGreenThresholdFormula_boundary_hasDerivAt (t₀ T : ℝ) (hT : t₀ ≤ T)
    {f : ℝ → ℂ} (hf : Continuous f) (hfT : ∀ u : ℝ, T < u → f u = 0) :
    HasDerivAt (cuspGreenThresholdFormula t₀ T f) (cuspGreenBoundaryTrace t₀ 0 f) t₀ := by
  convert hasDerivAt_cuspGreenThresholdFormula t₀ T hf t₀ using 1
  rw [cuspGreenBoundaryTrace_eq_interval t₀ T hT 0 hfT]
  simp

/-- The derivative trace is certified from the physical half-line at every parameter. -/
theorem hasDerivWithinAt_cuspGreenSolution_boundary {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t₀ : ℝ) (κ : ℂ) :
    HasDerivWithinAt (cuspGreenSolution t₀ κ f) (cuspGreenBoundaryTrace t₀ κ f)
      (Ici t₀) t₀ := by
  obtain ⟨T, hT, hfT⟩ := exists_cuspSource_cutoff hfc t₀
  by_cases hκ : κ = 0
  · subst κ
    have heq : cuspGreenSolution t₀ 0 f =ᶠ[𝓝[Ici t₀] t₀]
        cuspGreenThresholdFormula t₀ T f := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with v hv hvT
      exact cuspGreenSolution_zero_eq_formula t₀ T v hv hvT.le hf hfT
    exact (cuspGreenThresholdFormula_boundary_hasDerivAt t₀ T hT.le hf hfT).hasDerivWithinAt
      |>.congr_of_eventuallyEq_of_mem heq (by simp)
  · have heq : cuspGreenSolution t₀ κ f =ᶠ[𝓝[Ici t₀] t₀]
        cuspGreenSolutionFormula t₀ T κ f := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with v hv hvT
      exact cuspGreenSolution_eq_formula t₀ T v hv hvT.le hκ hf hfT
    have hd := hasDerivAt_cuspGreenSolutionFormula t₀ T hκ hf t₀
    rw [cuspGreenSolutionFormulaDeriv_boundary t₀ T hT.le κ hfT] at hd
    exact hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq (by simp)

/-- The actual right derivative, as an ordinary within-derivative value. -/
theorem derivWithin_cuspGreenSolution_boundary {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t₀ : ℝ) (κ : ℂ) :
    derivWithin (cuspGreenSolution t₀ κ f) (Ici t₀) t₀ = cuspGreenBoundaryTrace t₀ κ f :=
  (hasDerivWithinAt_cuspGreenSolution_boundary hf hfc t₀ κ).derivWithin
    (uniqueDiffWithinAt_Ici t₀)

end GapFamily.Analytic
