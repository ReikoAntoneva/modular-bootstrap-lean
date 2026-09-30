import GapFamily.Analytic.Cusp.Green.CuspGreenTrace

/-! Entire dependence and ordinary integral bounds for the actual boundary trace. -/

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Filter Set Metric
open scoped Topology

/-- The elementary trace kernel is uniformly bounded on a source collar and parameter disk. -/
theorem norm_cuspGreenBoundaryTraceKernel_le (t₀ U R u : ℝ) (κ : ℂ)
    (hu : t₀ ≤ u) (huU : u ≤ U) (hκ : ‖κ‖ ≤ R) :
    ‖Complex.exp (-κ * ((u - t₀ : ℝ) : ℂ))‖ ≤ Real.exp (R * (U - t₀)) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hκ
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (-κ * ((u - t₀ : ℝ) : ℂ)).re ≤ ‖-κ * ((u - t₀ : ℝ) : ℂ)‖ :=
      Complex.re_le_norm _
    _ = ‖κ‖ * (u - t₀) := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hu)]
    _ ≤ R * (u - t₀) := mul_le_mul_of_nonneg_right hκ (sub_nonneg.mpr hu)
    _ ≤ R * (U - t₀) := mul_le_mul_of_nonneg_left (sub_le_sub_right huU t₀) hR

/-- A finite source collar gives an explicit trace bound uniform through the threshold. -/
theorem norm_cuspGreenBoundaryTrace_on_disk_le (t₀ U R : ℝ) (κ : ℂ)
    (hκ : ‖κ‖ ≤ R) {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : ∀ u : ℝ, U < u → f u = 0) :
    ‖cuspGreenBoundaryTrace t₀ κ f‖ ≤
      Real.exp (R * (U - t₀)) * ∫ u : ℝ in Ioi t₀, ‖f u‖ := by
  unfold cuspGreenBoundaryTrace
  calc
    _ ≤ ∫ u : ℝ in Ioi t₀, Real.exp (R * (U - t₀)) * ‖f u‖ := by
      apply norm_integral_le_of_norm_le
        (((hf.integrable_of_hasCompactSupport hfc).norm.integrableOn).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      by_cases huU : u ≤ U
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (norm_cuspGreenBoundaryTraceKernel_le t₀ U R u κ hu.le huU hκ) (norm_nonneg _)
      · simp [hfU u (lt_of_not_ge huU)]
    _ = _ := integral_const_mul _ _

/-- The actual trace is bounded by the ordinary source mass throughout the closed right half-plane. -/
theorem norm_cuspGreenBoundaryTrace_halfplane_le (t₀ : ℝ) {κ : ℂ} (hκ : 0 ≤ κ.re)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ‖cuspGreenBoundaryTrace t₀ κ f‖ ≤ ∫ u : ℝ in Ioi t₀, ‖f u‖ := by
  unfold cuspGreenBoundaryTrace
  apply norm_integral_le_of_norm_le ((hf.integrable_of_hasCompactSupport hfc).norm.integrableOn)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have he : ‖Complex.exp (-κ * ((u - t₀ : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ) (sub_nonneg.mpr hu.le)
  simpa only [norm_mul, one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg (f u))

/-- Compact source support provides a proved integrable majorant on each parameter disk. -/
theorem cuspGreenBoundaryTrace_disk_domination (t₀ : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (κ₀ : ℂ) :
    ∃ b : ℝ → ℝ, Integrable b (volume.restrict (Ioi t₀)) ∧
      ∀ᵐ u : ℝ ∂volume.restrict (Ioi t₀),
        ∀ κ ∈ closedBall κ₀ 2,
          ‖Complex.exp (-κ * ((u - t₀ : ℝ) : ℂ)) * f u‖ ≤ b u := by
  obtain ⟨U, _, hfU⟩ := exists_cuspSource_cutoff hfc t₀
  refine ⟨fun u => Real.exp ((‖κ₀‖ + 2) * (U - t₀)) * ‖f u‖,
    (((hf.integrable_of_hasCompactSupport hfc).norm.integrableOn).const_mul _), ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  intro κ hκ
  have hκR : ‖κ‖ ≤ ‖κ₀‖ + 2 := norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hκ)
  by_cases huU : u ≤ U
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_cuspGreenBoundaryTraceKernel_le t₀ U (‖κ₀‖ + 2) u κ hu.le huU hκR)
      (norm_nonneg _)
  · simp [hfU u (lt_of_not_ge huU)]

/-- The actual derivative trace is entire in the spectral parameter, including zero. -/
theorem differentiable_cuspGreenBoundaryTrace_parameter (t₀ : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Differentiable ℂ (fun κ => cuspGreenBoundaryTrace t₀ κ f) := by
  apply differentiable_integral_of_entire_disk_bound
    (fun κ => (show Continuous (fun u : ℝ =>
      Complex.exp (-κ * ((u - t₀ : ℝ) : ℂ)) * f u) by fun_prop).aestronglyMeasurable) _
    (cuspGreenBoundaryTrace_disk_domination t₀ hf hfc)
  exact Eventually.of_forall fun u => by fun_prop

/-- Parameter differentiation commutes with the ordinary integral defining the trace. -/
theorem hasDerivAt_cuspGreenBoundaryTrace_parameter (t₀ : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (κ : ℂ) :
    Integrable (fun u : ℝ =>
      deriv (fun z : ℂ => Complex.exp (-z * ((u - t₀ : ℝ) : ℂ)) * f u) κ)
      (volume.restrict (Ioi t₀)) ∧
      HasDerivAt (fun z : ℂ => cuspGreenBoundaryTrace t₀ z f)
        (∫ u : ℝ in Ioi t₀,
          deriv (fun z : ℂ => Complex.exp (-z * ((u - t₀ : ℝ) : ℂ)) * f u) κ) κ := by
  exact hasDerivAt_integral_of_entire_disk_bound
    (fun z => (show Continuous (fun u : ℝ =>
      Complex.exp (-z * ((u - t₀ : ℝ) : ℂ)) * f u) by fun_prop).aestronglyMeasurable)
    (Eventually.of_forall fun u => by fun_prop)
    (cuspGreenBoundaryTrace_disk_domination t₀ hf hfc) κ

/-- Analyticity is for the genuine boundary response, with no assumed continuation. -/
theorem analyticAt_cuspGreenBoundaryTrace_parameter (t₀ : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (κ : ℂ) :
    AnalyticAt ℂ (fun z => cuspGreenBoundaryTrace t₀ z f) κ :=
  (differentiable_cuspGreenBoundaryTrace_parameter t₀ hf hfc).analyticAt κ

/-- At the threshold the trace converges to the ordinary total source mass. -/
theorem cuspGreenBoundaryTrace_tendsto_parameter_zero (t₀ : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun κ => cuspGreenBoundaryTrace t₀ κ f) (𝓝 (0 : ℂ))
      (𝓝 (∫ u : ℝ in Ioi t₀, f u)) := by
  simpa only [cuspGreenBoundaryTrace_zero] using
    (differentiable_cuspGreenBoundaryTrace_parameter t₀ hf hfc).continuous.tendsto 0

end GapFamily.Analytic
