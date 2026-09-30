import GapFamily.Analytic.Cusp.Green.CuspGreenSmoothForm
import GapFamily.Analytic.Cusp.Green.CuspGreenTrace

/-!
# First derivative reconstruction for the actual compact-source Green response

The established second-derivative equation is integrated from the genuine
boundary trace. The resulting primitive formula needs no outgoing-energy or
positive-real-part assumption on the nonzero spectral parameter.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory
open scoped Topology

private theorem cuspGreenSolution_nonpos {κ : ℂ} (hκ : κ ≠ 0)
    (f : ℝ → ℂ) {t : ℝ} (ht : t ≤ 0) :
    cuspGreenSolution 0 κ f t =
      ((Complex.exp (κ * (t : ℂ)) - Complex.exp (-κ * (t : ℂ))) / (2 * κ)) *
        cuspGreenBoundaryTrace 0 κ f := by
  unfold cuspGreenSolution cuspGreenBoundaryTrace
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have htu : t ≤ u := ht.trans hu.le
  dsimp only
  rw [cuspGreen_eq_quotient 0 t u hκ, abs_of_nonpos (sub_nonpos.mpr htu)]
  push_cast
  simp only [mul_zero, sub_zero]
  rw [show -κ * -((t : ℂ) - u) = κ * t + -κ * u by ring,
    show -κ * ((t : ℂ) + u) = -κ * t + -κ * u by ring,
    Complex.exp_add, Complex.exp_add]
  ring

/-- The literal Green integral is ordinarily differentiable at zero, from both sides. -/
theorem hasDerivAt_cuspGreenSolution_boundary_zero {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {κ : ℂ} (hκ : κ ≠ 0) :
    HasDerivAt (cuspGreenSolution 0 κ f) (cuspGreenBoundaryTrace 0 κ f) 0 := by
  have hexp (a : ℂ) : HasDerivAt (fun t : ℝ => Complex.exp (a * (t : ℂ))) a 0 := by
    simpa using (((Complex.hasDerivAt_exp (a * 0)).comp 0
      ((hasDerivAt_id (0 : ℂ)).const_mul a)).comp_ofReal)
  have hform : HasDerivAt (fun t : ℝ =>
      ((Complex.exp (κ * (t : ℂ)) - Complex.exp (-κ * (t : ℂ))) / (2 * κ)) *
        cuspGreenBoundaryTrace 0 κ f) (cuspGreenBoundaryTrace 0 κ f) 0 := by
    convert (((hexp κ).sub (hexp (-κ))).div_const (2 * κ)).mul_const
      (cuspGreenBoundaryTrace 0 κ f) using 1
    field_simp
    ring
  have hleft : HasDerivWithinAt (cuspGreenSolution 0 κ f)
      (cuspGreenBoundaryTrace 0 κ f) (Iic 0) 0 := by
    apply (hform.hasDerivWithinAt (s := Iic (0 : ℝ))).congr_of_mem
    · intro t ht
      exact cuspGreenSolution_nonpos hκ f ht
    · simp
  have hright := hasDerivWithinAt_cuspGreenSolution_boundary hf hfc 0 κ
  have hall := hleft.union hright
  rw [Iic_union_Ici] at hall
  exact hall.hasDerivAt Filter.univ_mem


/-- The differentiated finite formula is reconstructed from its actual trace and ODE. -/
theorem cuspGreenSolutionFormulaDeriv_eq_trace_primitive {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 T) {t : ℝ} (ht : 0 ≤ t) :
    cuspGreenSolutionFormulaDeriv 0 T κ f t =
      cuspGreenBoundaryTrace 0 κ f +
        κ ^ 2 * (∫ u in (0 : ℝ)..t, cuspGreenSolution 0 κ f u) -
          ∫ u in (0 : ℝ)..t, f u := by
  have hV : Continuous (cuspGreenSolutionFormula 0 T κ f) :=
    continuous_iff_continuousAt.mpr fun u =>
      (hasDerivAt_cuspGreenSolutionFormula 0 T hκ hf u).continuousAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_cuspGreenSolutionFormulaDeriv 0 T hf u)
    (((hV.const_mul (κ ^ 2)).sub hf).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_sub ((hV.const_mul (κ ^ 2)).intervalIntegrable 0 t)
      (hf.intervalIntegrable 0 t), intervalIntegral.integral_const_mul,
    cuspGreenSolutionFormulaDeriv_boundary 0 T hT κ
      (fun u hu => cuspGreenSmoothSource_zero_above hs hu.le)] at hFTC
  have hvalues : (∫ u in (0 : ℝ)..t, cuspGreenSolutionFormula 0 T κ f u) =
      ∫ u in (0 : ℝ)..t, cuspGreenSolution 0 κ f u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    exact cuspGreenSolutionFormula_eq_solution_of_support hT hκ hf hs hu.1
  rw [hvalues] at hFTC
  linear_combination -hFTC

/-- At every nonnegative position the inward derivative has the primitive value. -/
theorem hasDerivWithinAt_cuspGreenSolution_trace_primitive {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 T) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (cuspGreenSolution 0 κ f)
      (cuspGreenBoundaryTrace 0 κ f +
        κ ^ 2 * (∫ u in (0 : ℝ)..t, cuspGreenSolution 0 κ f u) -
          ∫ u in (0 : ℝ)..t, f u) (Ici 0) t := by
  have hd := (hasDerivAt_cuspGreenSolutionFormula 0 T hκ hf t).hasDerivWithinAt
    (s := Ici (0 : ℝ))
  rw [cuspGreenSolutionFormulaDeriv_eq_trace_primitive hT hκ hf hs ht] at hd
  exact hd.congr
    (fun u hu => (cuspGreenSolutionFormula_eq_solution_of_support hT hκ hf hs hu).symm)
    (cuspGreenSolutionFormula_eq_solution_of_support hT hκ hf hs ht).symm

/-- The ordinary derivative of the actual Green integral has the primitive value in the interior. -/
theorem hasDerivAt_cuspGreenSolution_trace_primitive {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 T) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cuspGreenSolution 0 κ f)
      (cuspGreenBoundaryTrace 0 κ f +
        κ ^ 2 * (∫ u in (0 : ℝ)..t, cuspGreenSolution 0 κ f u) -
          ∫ u in (0 : ℝ)..t, f u) t :=
  (hasDerivWithinAt_cuspGreenSolution_trace_primitive hT hκ hf hs ht.le).hasDerivAt
    (Ici_mem_nhds ht)

/-- The total derivative agrees with the certified primitive on the physical interior. -/
theorem deriv_cuspGreenSolution_eq_trace_primitive {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 T) {t : ℝ} (ht : 0 < t) :
    deriv (cuspGreenSolution 0 κ f) t =
      cuspGreenBoundaryTrace 0 κ f +
        κ ^ 2 * (∫ u in (0 : ℝ)..t, cuspGreenSolution 0 κ f u) -
          ∫ u in (0 : ℝ)..t, f u :=
  (hasDerivAt_cuspGreenSolution_trace_primitive hT hκ hf hs ht).deriv

/-- The ordinary derivative formula also holds at the boundary point. -/
theorem hasDerivAt_cuspGreenSolution_trace_primitive_nonneg {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 T) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (cuspGreenSolution 0 κ f)
      (cuspGreenBoundaryTrace 0 κ f +
        κ ^ 2 * (∫ u in (0 : ℝ)..t, cuspGreenSolution 0 κ f u) -
          ∫ u in (0 : ℝ)..t, f u) t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · have hfc : HasCompactSupport f :=
      isCompact_Icc.of_isClosed_subset isClosed_closure (hs.trans Ioo_subset_Icc_self)
    simpa only [intervalIntegral.integral_same, mul_zero, add_zero, sub_zero] using
      hasDerivAt_cuspGreenSolution_boundary_zero hf hfc hκ
  · exact hasDerivAt_cuspGreenSolution_trace_primitive hT hκ hf hs ht

/-- The certified reconstruction is the total derivative on the closed physical half-line. -/
theorem deriv_cuspGreenSolution_eq_trace_primitive_nonneg {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 T) {t : ℝ} (ht : 0 ≤ t) :
    deriv (cuspGreenSolution 0 κ f) t =
      cuspGreenBoundaryTrace 0 κ f +
        κ ^ 2 * (∫ u in (0 : ℝ)..t, cuspGreenSolution 0 κ f u) -
          ∫ u in (0 : ℝ)..t, f u :=
  (hasDerivAt_cuspGreenSolution_trace_primitive_nonneg hT hκ hf hs ht).deriv

end GapFamily.Analytic
