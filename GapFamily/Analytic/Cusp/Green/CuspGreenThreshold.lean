import GapFamily.Analytic.Cusp.Green.CuspGreenSolution

/-!
# The scalar cusp solution at the threshold

At zero spectral parameter the actual kernel is `min t u - t₀`.
Its compact-source integral has a finite formula with no division by the
spectral parameter. Differentiating that formula supplies the forced equation
at the threshold and hence for every complex parameter.
-/

noncomputable section

namespace GapFamily.Analytic

open Filter MeasureTheory Set
open scoped Topology

/-- The finite threshold solution, including both sides of the source point. -/
def cuspGreenThresholdFormula (t₀ T : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (∫ u in t₀..t, ((u : ℂ) - (t₀ : ℂ)) * f u) +
    ((t : ℂ) - (t₀ : ℂ)) * ∫ u in t..T, f u

/-- The threshold formula differentiates to the remaining source integral. -/
theorem hasDerivAt_cuspGreenThresholdFormula
    (t₀ T : ℝ) {f : ℝ → ℂ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (cuspGreenThresholdFormula t₀ T f) (∫ u in t..T, f u) t := by
  have hp : Continuous (fun u : ℝ => ((u : ℂ) - (t₀ : ℂ)) * f u) := by fun_prop
  have ha := intervalIntegral.integral_hasDerivAt_right
    (hp.intervalIntegrable t₀ t) (hp.stronglyMeasurableAtFilter volume (𝓝 t)) hp.continuousAt
  have hb := intervalIntegral.integral_hasDerivAt_left
    (hf.intervalIntegrable t T) (hf.stronglyMeasurableAtFilter volume (𝓝 t)) hf.continuousAt
  have hc : HasDerivAt (fun u : ℝ => (u : ℂ) - (t₀ : ℂ)) 1 t :=
    ((hasDerivAt_id (t : ℂ)).sub_const (t₀ : ℂ)).comp_ofReal
  apply (ha.add (hc.mul hb)).congr_deriv
  ring

/-- The second derivative of the threshold formula is the negative source. -/
theorem hasDerivAt_deriv_cuspGreenThresholdFormula
    (t₀ T : ℝ) {f : ℝ → ℂ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (deriv (cuspGreenThresholdFormula t₀ T f)) (-f t) t := by
  have heq : deriv (cuspGreenThresholdFormula t₀ T f) =
      fun v => ∫ u in v..T, f u :=
    funext fun v => (hasDerivAt_cuspGreenThresholdFormula t₀ T hf v).deriv
  rw [heq]
  exact intervalIntegral.integral_hasDerivAt_left
    (hf.intervalIntegrable t T) (hf.stronglyMeasurableAtFilter volume (𝓝 t)) hf.continuousAt

/-- The finite threshold formula is the actual half-line Green integral. -/
theorem cuspGreenSolution_zero_eq_formula (t₀ T t : ℝ) (ht₀ : t₀ ≤ t) (htT : t ≤ T)
    {f : ℝ → ℂ} (hf : Continuous f) (hfT : ∀ u, T < u → f u = 0) :
    cuspGreenSolution t₀ 0 f t = cuspGreenThresholdFormula t₀ T f t := by
  have hk : Continuous (fun u : ℝ => cuspGreen t₀ t u 0 * f u) :=
    (cuspGreen_continuous_source t₀ t 0).mul hf
  have hleft : (∫ u in t₀..t, cuspGreen t₀ t u 0 * f u) =
      ∫ u in t₀..t, ((u : ℂ) - (t₀ : ℂ)) * f u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht₀] at hu
    dsimp only
    rw [cuspGreen_zero, min_eq_right hu.2, Complex.ofReal_sub]
  have hright : (∫ u in t..T, cuspGreen t₀ t u 0 * f u) =
      ((t : ℂ) - (t₀ : ℂ)) * ∫ u in t..T, f u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le htT] at hu
    dsimp only
    rw [cuspGreen_zero, min_eq_left hu.1, Complex.ofReal_sub]
  rw [cuspGreenSolution_eq_interval t₀ T t (ht₀.trans htT) 0 hfT,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hk.intervalIntegrable t₀ t) (hk.intervalIntegrable t T), hleft, hright]
  rfl

/-- The actual threshold response is differentiable in the physical interior. -/
theorem cuspGreenSolution_zero_differentiableAt {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) {t : ℝ} (ht : t₀ < t) :
    DifferentiableAt ℝ (cuspGreenSolution t₀ 0 f) t := by
  obtain ⟨T, htT, hfT⟩ := exists_cuspSource_cutoff hfc t
  have heq : cuspGreenSolution t₀ 0 f =ᶠ[𝓝 t] cuspGreenThresholdFormula t₀ T f := by
    filter_upwards [Ioo_mem_nhds ht htT] with v hv
    exact cuspGreenSolution_zero_eq_formula t₀ T v hv.1.le hv.2.le hf hfT
  exact ((hasDerivAt_cuspGreenThresholdFormula t₀ T hf t).congr_of_eventuallyEq
    heq).differentiableAt

/-- The actual threshold integral has second derivative equal to the negative source. -/
theorem hasDerivAt_deriv_cuspGreenSolution_zero {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) {t : ℝ} (ht : t₀ < t) :
    HasDerivAt (deriv (cuspGreenSolution t₀ 0 f)) (-f t) t := by
  obtain ⟨T, htT, hfT⟩ := exists_cuspSource_cutoff hfc t
  have heq : cuspGreenSolution t₀ 0 f =ᶠ[𝓝 t] cuspGreenThresholdFormula t₀ T f := by
    filter_upwards [Ioo_mem_nhds ht htT] with v hv
    exact cuspGreenSolution_zero_eq_formula t₀ T v hv.1.le hv.2.le hf hfT
  exact (hasDerivAt_deriv_cuspGreenThresholdFormula t₀ T hf t).congr_of_eventuallyEq heq.deriv

/-- The threshold integral has a continuous Dirichlet trace. -/
theorem cuspGreenSolution_zero_continuousWithinAt_boundary {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t₀ : ℝ) :
    ContinuousWithinAt (cuspGreenSolution t₀ 0 f) (Ici t₀) t₀ := by
  obtain ⟨T, hT, hfT⟩ := exists_cuspSource_cutoff hfc t₀
  have heq : cuspGreenSolution t₀ 0 f =ᶠ[𝓝[Ici t₀] t₀]
      cuspGreenThresholdFormula t₀ T f := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with v hv hvT
    exact cuspGreenSolution_zero_eq_formula t₀ T v hv (le_of_lt hvT) hf hfT
  exact (hasDerivAt_cuspGreenThresholdFormula t₀ T hf t₀).continuousAt.continuousWithinAt
    |>.congr_of_eventuallyEq heq
      (cuspGreenSolution_zero_eq_formula t₀ T t₀ le_rfl hT.le hf hfT)

/-- Interior differentiability holds for every complex spectral parameter. -/
theorem cuspGreenSolution_differentiableAt_all {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) (κ : ℂ) {t : ℝ} (ht : t₀ < t) :
    DifferentiableAt ℝ (cuspGreenSolution t₀ κ f) t := by
  by_cases hκ : κ = 0
  · subst κ
    exact cuspGreenSolution_zero_differentiableAt hf hfc t₀ ht
  · exact cuspGreenSolution_differentiableAt hf hfc t₀ hκ ht

/-- The actual second-derivative certificate extends through the threshold. -/
theorem hasDerivAt_deriv_cuspGreenSolution_all {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) (κ : ℂ) {t : ℝ} (ht : t₀ < t) :
    HasDerivAt (deriv (cuspGreenSolution t₀ κ f))
      (κ ^ 2 * cuspGreenSolution t₀ κ f t - f t) t := by
  by_cases hκ : κ = 0
  · subst κ
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_sub] using
      hasDerivAt_deriv_cuspGreenSolution_zero hf hfc t₀ ht
  · exact hasDerivAt_deriv_cuspGreenSolution hf hfc t₀ hκ ht

/-- The genuine forced equation holds at every complex spectral parameter. -/
theorem cuspGreenSolution_forcedODE_all {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) (κ : ℂ) {t : ℝ} (ht : t₀ < t) :
    -deriv (deriv (cuspGreenSolution t₀ κ f)) t +
      κ ^ 2 * cuspGreenSolution t₀ κ f t = f t := by
  rw [(hasDerivAt_deriv_cuspGreenSolution_all hf hfc t₀ κ ht).deriv]
  ring

/-- The physical boundary trace is continuous for every complex parameter. -/
theorem cuspGreenSolution_continuousWithinAt_boundary_all {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t₀ : ℝ) (κ : ℂ) :
    ContinuousWithinAt (cuspGreenSolution t₀ κ f) (Ici t₀) t₀ := by
  by_cases hκ : κ = 0
  · subst κ
    exact cuspGreenSolution_zero_continuousWithinAt_boundary hf hfc t₀
  · exact cuspGreenSolution_continuousWithinAt_boundary hf hfc t₀ hκ

/-- The Dirichlet value is the genuine right limit, including at the threshold. -/
theorem cuspGreenSolution_tendsto_boundary_all {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t₀ : ℝ) (κ : ℂ) :
    Tendsto (cuspGreenSolution t₀ κ f) (𝓝[>] t₀) (𝓝 0) := by
  have hc := (cuspGreenSolution_continuousWithinAt_boundary_all hf hfc t₀ κ).mono
    Ioi_subset_Ici_self
  simpa only [ContinuousWithinAt, cuspGreenSolution_boundary] using hc

end GapFamily.Analytic
