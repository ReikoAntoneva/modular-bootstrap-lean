import GapFamily.Analytic.Cusp.Profile.CuspWeightedSchurContinuation
import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurGradient
import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedFrameLocal

/-!
# Continued gradients for the actual weighted Schur response

The source is the genuine noncompact weighted vector. Only the original
solution's gradient output is cut by height; the output indicator is never
differentiated. The Schur trace vectors remain those of the constant response.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurWeighted

open CuspSchurLocal

def localGradientZeroX (α : ℝ) (hα : 0 ≤ α) (L _T : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  ((modularLowCut (Real.exp L)).comp (constrainedGradientX κ)).comp
    (cuspWeightedInput α hα)

def localGradientZeroY (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  ((modularLowCut (Real.exp L)).comp (constrainedGradientY κ)).comp
      (cuspWeightedInput α hα) +
    (cuspGreenWeightedFrameLocalOutput α hα L T κ).comp cuspHalfLineSourceCoefficient

def continuedLocalSchurGradientX (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  localGradientZeroX α hα L T κ +
    ((CuspSchur.continuedDenominator κ)⁻¹ • localNumerator α hα κ).smulRight
      (localGradientTraceX L κ)

def continuedLocalSchurGradientY (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  localGradientZeroY α hα L T κ +
    ((CuspSchur.continuedDenominator κ)⁻¹ • localNumerator α hα κ).smulRight
      (localGradientTraceY L κ)

private theorem analyticAt_comp_clm
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {a : ℂ} {f : ℂ → (F →L[ℂ] G)} {g : ℂ → (E →L[ℂ] F)}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) :
    AnalyticAt ℂ (fun z => (f z).comp (g z)) a :=
  ((ContinuousLinearMap.compL ℂ E F G).analyticAt_bilinear _).comp (hf.prod hg)

theorem localGradientZeroX_analyticAt_zero (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) :
    AnalyticAt ℂ (localGradientZeroX α hα L T) 0 :=
  analyticAt_comp_clm
    (analyticAt_comp_clm analyticAt_const constrainedGradientX_analyticAt_zero)
    analyticAt_const

theorem localGradientZeroY_analyticAt_zero {α : ℝ} (hα : 0 < α) (L T : ℝ) :
    AnalyticAt ℂ (localGradientZeroY α hα.le L T) 0 :=
  (analyticAt_comp_clm
    (analyticAt_comp_clm analyticAt_const constrainedGradientY_analyticAt_zero)
    analyticAt_const).add
      (analyticAt_comp_clm
        (analyticAt_cuspGreenWeightedFrameLocalOutput α hα.le L T (by simpa using hα))
        analyticAt_const)

theorem continuedLocalSchurGradientX_analyticAt_zero {α : ℝ} (hα : 0 < α) (L T : ℝ) :
    AnalyticAt ℂ (continuedLocalSchurGradientX α hα.le L T) 0 := by
  have hc := CuspSchur.continuedDenominator_inverse_analyticAt_threshold.smul
    (localNumerator_analyticAt_zero hα)
  have hp := hc.prod (localGradientTraceX_analyticAt_zero L)
  have hb := (ContinuousLinearMap.smulRightL ℂ ModularHilbert ModularHilbert).analyticAt_bilinear
    (((CuspSchur.continuedDenominator 0)⁻¹ • localNumerator α hα.le 0),
      localGradientTraceX L 0)
  have hR := hb.comp_of_eq hp rfl
  have hsum := (localGradientZeroX_analyticAt_zero α hα.le L T).add hR
  exact hsum

theorem continuedLocalSchurGradientY_analyticAt_zero {α : ℝ} (hα : 0 < α) (L T : ℝ) :
    AnalyticAt ℂ (continuedLocalSchurGradientY α hα.le L T) 0 := by
  have hc := CuspSchur.continuedDenominator_inverse_analyticAt_threshold.smul
    (localNumerator_analyticAt_zero hα)
  have hp := hc.prod (localGradientTraceY_analyticAt_zero L)
  have hb := (ContinuousLinearMap.smulRightL ℂ ModularHilbert ModularHilbert).analyticAt_bilinear
    (((CuspSchur.continuedDenominator 0)⁻¹ • localNumerator α hα.le 0),
      localGradientTraceY L 0)
  have hR := hb.comp_of_eq hp rfl
  have hsum := (localGradientZeroY_analyticAt_zero hα L T).add hR
  exact hsum

end GapFamily.Analytic.CuspSchurWeighted
