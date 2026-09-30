import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurGradientBasic
import GapFamily.Analytic.Cusp.Scalar.CuspConstantLocalGradient
import GapFamily.Analytic.Cusp.Green.CuspGreenFrameOutput

/-!
# Continued finite-height gradient of the actual Schur response

The two fields restrict the gradient of the original physical solution. The
sharp output height cut is applied after differentiation. Actual scalar Green
and constant-response derivatives supply the vertical channel at threshold.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal

def localGradientZeroX (L T : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  ((modularLowCut (Real.exp L)).comp (constrainedGradientX κ)).comp
    (modularLowCut (Real.exp T))

def localGradientZeroY (L T : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  ((modularLowCut (Real.exp L)).comp (constrainedGradientY κ)).comp
    (modularLowCut (Real.exp T)) + cuspGreenFrameLocalizedOutput L T κ

def localGradientTraceX (L : ℝ) (κ : ℂ) : ModularHilbert :=
  parameter κ • modularLowCut (Real.exp L) (constrainedGradientX κ modularConstant)

def localGradientTraceY (L : ℝ) (κ : ℂ) : ModularHilbert :=
  parameter κ •
    (modularLowCut (Real.exp L) (constrainedGradientY κ modularConstant) +
      cuspConstantLocalVerticalGradient L κ)

def continuedLocalSchurGradientX (L T : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  localGradientZeroX L T κ +
    ((CuspSchur.continuedDenominator κ)⁻¹ • localNumerator T κ).smulRight
      (localGradientTraceX L κ)

def continuedLocalSchurGradientY (L T : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  localGradientZeroY L T κ +
    ((CuspSchur.continuedDenominator κ)⁻¹ • localNumerator T κ).smulRight
      (localGradientTraceY L κ)

private theorem analyticAt_comp_clm
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {a : ℂ} {f : ℂ → (F →L[ℂ] G)} {g : ℂ → (E →L[ℂ] F)}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) :
    AnalyticAt ℂ (fun z => (f z).comp (g z)) a :=
  ((ContinuousLinearMap.compL ℂ E F G).analyticAt_bilinear _).comp (hf.prod hg)

theorem localGradientZeroX_analyticAt_zero (L T : ℝ) :
    AnalyticAt ℂ (localGradientZeroX L T) 0 :=
  analyticAt_comp_clm
    (analyticAt_comp_clm analyticAt_const constrainedGradientX_analyticAt_zero)
    analyticAt_const

theorem localGradientZeroY_analyticAt_zero (L T : ℝ) :
    AnalyticAt ℂ (localGradientZeroY L T) 0 :=
  (analyticAt_comp_clm
    (analyticAt_comp_clm analyticAt_const constrainedGradientY_analyticAt_zero)
    analyticAt_const).add (analyticAt_cuspGreenFrameLocalizedOutput L T 0)

theorem localGradientTraceX_analyticAt_zero (L : ℝ) :
    AnalyticAt ℂ (localGradientTraceX L) 0 := by
  have hq : AnalyticAt ℂ (fun κ => constrainedGradientX κ modularConstant) 0 :=
    ((ContinuousLinearMap.apply ℂ ModularHilbert modularConstant).analyticAt _).comp
      constrainedGradientX_analyticAt_zero
  have hl : AnalyticAt ℂ
      (fun κ => modularLowCut (Real.exp L) (constrainedGradientX κ modularConstant)) 0 :=
    ((modularLowCut (Real.exp L)).analyticAt _).comp hq
  exact (parameter_analyticAt 0).smul hl

theorem localGradientTraceY_analyticAt_zero (L : ℝ) :
    AnalyticAt ℂ (localGradientTraceY L) 0 := by
  have hq : AnalyticAt ℂ (fun κ => constrainedGradientY κ modularConstant) 0 :=
    ((ContinuousLinearMap.apply ℂ ModularHilbert modularConstant).analyticAt _).comp
      constrainedGradientY_analyticAt_zero
  have hl : AnalyticAt ℂ
      (fun κ => modularLowCut (Real.exp L) (constrainedGradientY κ modularConstant)) 0 :=
    ((modularLowCut (Real.exp L)).analyticAt _).comp hq
  exact (parameter_analyticAt 0).smul
    (hl.add (cuspConstantLocalVerticalGradient_analyticAt_zero L))

theorem continuedLocalSchurGradientX_analyticAt_zero (L T : ℝ) :
    AnalyticAt ℂ (continuedLocalSchurGradientX L T) 0 := by
  have hc := CuspSchur.continuedDenominator_inverse_analyticAt_threshold.smul
    (localNumerator_analyticAt_zero T)
  have hp := hc.prod (localGradientTraceX_analyticAt_zero L)
  have hR := (ContinuousLinearMap.smulRightL ℂ ModularHilbert ModularHilbert).analyticAt_bilinear
    (((CuspSchur.continuedDenominator 0)⁻¹ • localNumerator T 0), localGradientTraceX L 0)
  have hr := hR.comp_of_eq hp rfl
  exact (localGradientZeroX_analyticAt_zero L T).add hr

theorem continuedLocalSchurGradientY_analyticAt_zero (L T : ℝ) :
    AnalyticAt ℂ (continuedLocalSchurGradientY L T) 0 := by
  have hc := CuspSchur.continuedDenominator_inverse_analyticAt_threshold.smul
    (localNumerator_analyticAt_zero T)
  have hp := hc.prod (localGradientTraceY_analyticAt_zero L)
  have hR := (ContinuousLinearMap.smulRightL ℂ ModularHilbert ModularHilbert).analyticAt_bilinear
    (((CuspSchur.continuedDenominator 0)⁻¹ • localNumerator T 0), localGradientTraceY L 0)
  have hr := hR.comp_of_eq hp rfl
  exact (localGradientZeroY_analyticAt_zero L T).add hr

end GapFamily.Analytic.CuspSchurLocal
