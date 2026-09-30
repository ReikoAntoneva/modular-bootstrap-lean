import GapFamily.Analytic.Cusp.Green.CuspGreenFirstOperator
import GapFamily.Analytic.Cusp.Profile.CuspCollarPrimitiveInterval
import GapFamily.Analytic.Cusp.Green.CuspGreenSmoothFirst
import GapFamily.Analytic.Cusp.Green.CuspGreenPhysicalWeak

/-! Identification of the entire first-derivative operator with the ordinary
first derivative of the actual compact-source Green integral. -/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory
open scoped Topology

/-- Continuous-source mixed values retain the actual half-line Green integral. -/
theorem cuspGreenMixedOperator_apply_source {L T : ℝ} (hT : 0 ≤ T) (κ : ℂ)
    {f : ℝ → ℂ} (hf : Continuous f) (hs : tsupport f ⊆ Ioo 0 T)
    (t : CuspGreenCollar 0 L) :
    cuspGreenMixedOperator L T κ (cuspGreenCollarSource 0 T f hf) t =
      cuspGreenSolution 0 κ f t := by
  rw [cuspGreenMixedOperator_eq_response]
  exact cuspGreenCollarResponse_source_eq_solution T hT κ f hf
    (fun u hu => cuspGreenSmoothSource_zero_above hs hu.le) t

/-- The entire reconstruction equals the actual differentiated finite formula. -/
theorem cuspGreenFirstOperator_apply_source {L T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 T) (t : CuspGreenCollar 0 L) :
    cuspGreenFirstOperator L T κ (cuspGreenCollarSource 0 T f hf) t =
      cuspGreenSolutionFormulaDeriv 0 T κ f t := by
  rw [cuspGreenFirstOperator_apply,
    cuspGreenCollarTraceOperator_eq_trace 0 T hT κ f hf
      (fun u hu => cuspGreenSmoothSource_zero_above hs hu.le),
    cuspCollarPrimitive_source_eq_intervalIntegral L T f hf
      (fun u hu => cuspGreenSmoothSource_zero_above hs hu.le),
    cuspGreenSolutionFormulaDeriv_eq_trace_primitive hT hκ hf hs t.property.1]
  congr 2
  congr 1
  exact cuspCollarPrimitive_toLp_eq_intervalIntegral L
    (cuspGreenMixedOperator L T κ (cuspGreenCollarSource 0 T f hf))
    (cuspGreenSolution 0 κ f) (cuspGreenMixedOperator_apply_source hT κ hf hs) t

/-- The source derivative is genuine, including at the boundary point. -/
theorem hasDerivAt_cuspGreenSolution_firstOperator {L T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 T) (t : CuspGreenCollar 0 L) :
    HasDerivAt (cuspGreenSolution 0 κ f)
      (cuspGreenFirstOperator L T κ (cuspGreenCollarSource 0 T f hf) t) t := by
  rw [cuspGreenFirstOperator_apply_source hT hκ hf hs,
    cuspGreenSolutionFormulaDeriv_eq_trace_primitive hT hκ hf hs t.property.1]
  exact hasDerivAt_cuspGreenSolution_trace_primitive_nonneg hT hκ hf hs t.property.1

/-- The shifted ordinary derivative gives the exact continuous frame profile. -/
theorem cuspGreenFrameOperator_apply_source {L T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 T) (t : CuspGreenCollar 0 L) :
    cuspGreenFrameOperator L T κ (cuspGreenCollarSource 0 T f hf) t =
      cuspGreenSolutionFormulaDeriv 0 T κ f t +
        (1 / 2 : ℂ) * cuspGreenSolutionFormula 0 T κ f t := by
  rw [cuspGreenFrameOperator_apply, cuspGreenFirstOperator_apply_source hT hκ hf hs,
    cuspGreenMixedOperator_apply_source hT κ hf hs,
    cuspGreenSolutionFormula_eq_solution_of_support hT hκ hf hs t.property.1]

end GapFamily.Analytic
