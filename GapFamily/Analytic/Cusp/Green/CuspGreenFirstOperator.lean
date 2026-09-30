import GapFamily.Analytic.Cusp.Profile.CuspCollarPrimitive
import GapFamily.Analytic.Cusp.Green.CuspGreenMixedOperator
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorTraceAnalytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Entire first-derivative operators on independent finite collars

The boundary trace and a bounded ordinary primitive reconstruct the first
logarithmic derivative from the genuine second-derivative equation. The
parameter dependence is in the operator norm with continuous output.
-/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory Filter
open scoped Topology

/-- Boundary trace plus the ordinary primitive of `κ² V - f`. -/
def cuspGreenFirstOperator (L T : ℝ) (κ : ℂ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ) :=
  (ContinuousLinearMap.const ℂ (CuspGreenCollar 0 L)).comp
      (cuspGreenCollarTraceOperator 0 T κ) +
    κ ^ 2 • ((cuspCollarPrimitive L L).comp (cuspGreenMixedL2Operator L T κ)) -
      cuspCollarPrimitive L T

/-- Every source has the literal convergent trace-plus-primitive value. -/
theorem cuspGreenFirstOperator_apply (L T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (t : CuspGreenCollar 0 L) :
    cuspGreenFirstOperator L T κ f t = cuspGreenCollarTraceOperator 0 T κ f +
      κ ^ 2 * cuspCollarPrimitive L L (cuspGreenMixedL2Operator L T κ f) t -
        cuspCollarPrimitive L T f t := rfl

/-- Entire dependence holds in the actual continuous-output operator norm. -/
theorem differentiable_cuspGreenFirstOperator (L T : ℝ) :
    Differentiable ℂ (cuspGreenFirstOperator L T) := by
  have : IsBoundedSMul ℂ (Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ)) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℂ) (E := Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ))
  have hb : Differentiable ℂ (fun κ : ℂ =>
      (ContinuousLinearMap.const ℂ (CuspGreenCollar 0 L)).comp
        (cuspGreenCollarTraceOperator 0 T κ)) :=
    (differentiable_const (ContinuousLinearMap.const ℂ (CuspGreenCollar 0 L))).clm_comp
      (differentiable_cuspGreenCollarTraceOperator 0 T)
  have hp : Differentiable ℂ (fun κ : ℂ =>
      (cuspCollarPrimitive L L).comp (cuspGreenMixedL2Operator L T κ)) :=
    (differentiable_const (cuspCollarPrimitive L L)).clm_comp
      (differentiable_cuspGreenMixedL2Operator L T)
  have hs : Differentiable ℂ (fun κ : ℂ => κ ^ 2 •
      ((cuspCollarPrimitive L L).comp (cuspGreenMixedL2Operator L T κ))) :=
    Differentiable.smul (𝕜 := ℂ)
      (F := Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ))
      (differentiable_id.pow 2) hp
  exact Differentiable.sub (𝕜 := ℂ)
    (F := Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ))
    (hb.add hs) (differentiable_const (cuspCollarPrimitive L T))

theorem analyticAt_cuspGreenFirstOperator (L T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenFirstOperator L T) κ :=
  (differentiable_cuspGreenFirstOperator L T).analyticAt κ

/-- The shifted logarithmic derivative is the physical vertical-frame profile. -/
def cuspGreenFrameOperator (L T : ℝ) (κ : ℂ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ) :=
  cuspGreenFirstOperator L T κ + (1 / 2 : ℂ) • cuspGreenMixedOperator L T κ

theorem cuspGreenFrameOperator_apply (L T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (t : CuspGreenCollar 0 L) :
    cuspGreenFrameOperator L T κ f t = cuspGreenFirstOperator L T κ f t +
      (1 / 2 : ℂ) * cuspGreenMixedOperator L T κ f t := rfl

theorem differentiable_cuspGreenFrameOperator (L T : ℝ) :
    Differentiable ℂ (cuspGreenFrameOperator L T) := by
  unfold cuspGreenFrameOperator
  exact (differentiable_cuspGreenFirstOperator L T).add
    (Differentiable.const_smul (𝕜 := ℂ)
      (F := Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ))
      (differentiable_cuspGreenMixedOperator L T) (1 / 2 : ℂ))

theorem analyticAt_cuspGreenFrameOperator (L T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenFrameOperator L T) κ :=
  (differentiable_cuspGreenFrameOperator L T).analyticAt κ

end GapFamily.Analytic
