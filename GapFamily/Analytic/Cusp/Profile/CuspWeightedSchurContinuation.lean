import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedLocal
import GapFamily.Analytic.Cusp.Profile.CuspWeightedConstantPhysical
import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurContinuation

/-! The actual Schur formula with a noncompact exponentially weighted source
and a finite output window. The auxiliary finite source collar only enters the
proved scalar Green split. -/

noncomputable section
namespace GapFamily.Analytic.CuspSchurWeighted
open CuspSchurLocal

def localZeroTrace (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  ((modularLowCut (Real.exp L)).comp (constrainedResponse κ)).comp
      (cuspWeightedInput α hα) +
    (cuspGreenWeightedLocalOutput α hα L T κ).comp cuspHalfLineSourceCoefficient

def localNumerator (α : ℝ) (hα : 0 ≤ α) (κ : ℂ) : ModularHilbert →L[ℂ] ℂ :=
  (innerSL ℂ modularConstant).comp (cuspWeightedInput α hα) + parameter κ •
    (((innerSL ℂ modularConstant).comp (constrainedResponse κ)).comp
      (cuspWeightedInput α hα) + cuspWeightedConstantPairingFunctional α κ)

/-- A concrete bounded local Schur response for all exponentially weighted Hilbert sources. -/
def continuedLocalSchur (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  localZeroTrace α hα L T κ +
    ((CuspSchur.continuedDenominator κ)⁻¹ • localNumerator α hα κ).smulRight
      (localTraceVector L κ)

private theorem analyticAt_comp_clm
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {a : ℂ} {f : ℂ → (F →L[ℂ] G)} {g : ℂ → (E →L[ℂ] F)}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) :
    AnalyticAt ℂ (fun z => (f z).comp (g z)) a :=
  ((ContinuousLinearMap.compL ℂ E F G).analyticAt_bilinear _).comp (hf.prod hg)

theorem localZeroTrace_analyticAt_zero {α : ℝ} (hα : 0 < α) (L T : ℝ) :
    AnalyticAt ℂ (localZeroTrace α hα.le L T) 0 :=
  (analyticAt_comp_clm
    (analyticAt_comp_clm analyticAt_const constrainedResponse_analyticAt_zero)
    analyticAt_const).add
      (analyticAt_comp_clm
        (analyticAt_cuspGreenWeightedLocalOutput α hα.le L T (by simpa using hα))
        analyticAt_const)

theorem localNumerator_analyticAt_zero {α : ℝ} (hα : 0 < α) :
    AnalyticAt ℂ (localNumerator α hα.le) 0 :=
  analyticAt_const.add ((parameter_analyticAt 0).smul
    ((analyticAt_comp_clm
      (analyticAt_comp_clm analyticAt_const constrainedResponse_analyticAt_zero)
      analyticAt_const).add (cuspWeightedConstantPairingFunctional_analyticAt_zero hα)))

/-- Norm analyticity through threshold for the full weighted local Schur formula. -/
theorem continuedLocalSchur_analyticAt_zero {α : ℝ} (hα : 0 < α) (L T : ℝ) :
    AnalyticAt ℂ (continuedLocalSchur α hα.le L T) 0 := by
  have hc := CuspSchur.continuedDenominator_inverse_analyticAt_threshold.smul
    (localNumerator_analyticAt_zero hα)
  have hp := hc.prod (localTraceVector_analyticAt_zero L)
  have hr := (ContinuousLinearMap.smulRightL ℂ ModularHilbert ModularHilbert).analyticAt_bilinear
    (((CuspSchur.continuedDenominator 0)⁻¹ • localNumerator α hα.le 0), localTraceVector L 0)
  have hR := hr.comp_of_eq hp rfl
  have hsum := (localZeroTrace_analyticAt_zero hα L T).add hR
  exact hsum

end GapFamily.Analytic.CuspSchurWeighted
