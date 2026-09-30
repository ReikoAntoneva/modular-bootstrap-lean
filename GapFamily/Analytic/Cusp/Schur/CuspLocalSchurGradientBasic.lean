import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurContinuation
import GapFamily.Analytic.Cusp.Scalar.CuspScalarHorizontalGradient

/-!
# Actual constrained gradient channels near threshold

The source solution takes values in the actual completed constrained form
space. Bounded closed-gradient components therefore inherit its analyticity.
These are gradients of the original solution, before any output height cut.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal
open ModularGradient

def constrainedGradientX (κ : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  ((WithLp.fstL 2 ℂ ModularHilbert ModularHilbert).comp cuspMeanZeroGradient).comp
    (cuspMeanZeroPencilSolution (parameter κ))

def constrainedGradientY (κ : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  ((WithLp.sndL 2 ℂ ModularHilbert ModularHilbert).comp cuspMeanZeroGradient).comp
    (cuspMeanZeroPencilSolution (parameter κ))

private theorem constrainedGradientPostcompose_analyticAt_zero
    (D : cuspMeanZeroForm →L[ℂ] ModularHilbert) :
    AnalyticAt ℂ (fun κ => D.comp (cuspMeanZeroPencilSolution (parameter κ))) 0 := by
  have hs : AnalyticAt ℂ (fun κ => cuspMeanZeroPencilSolution (parameter κ)) 0 := by
    apply (cuspMeanZeroPencilSolution_analyticAt cuspMeanZeroPencil_isUnit_quarter).comp_of_eq
      (parameter_analyticAt 0)
    norm_num [parameter]
  let P : (ModularHilbert →L[ℂ] cuspMeanZeroForm) →L[ℂ]
      (ModularHilbert →L[ℂ] ModularHilbert) :=
    ContinuousLinearMap.compL ℂ ModularHilbert cuspMeanZeroForm ModularHilbert D
  have hP := ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := ModularHilbert →L[ℂ] cuspMeanZeroForm)
    (F := ModularHilbert →L[ℂ] ModularHilbert) P
      (cuspMeanZeroPencilSolution (parameter 0))
  exact hP.comp_of_eq hs rfl

theorem constrainedGradientX_analyticAt_zero : AnalyticAt ℂ constrainedGradientX 0 :=
  constrainedGradientPostcompose_analyticAt_zero _

theorem constrainedGradientY_analyticAt_zero : AnalyticAt ℂ constrainedGradientY 0 :=
  constrainedGradientPostcompose_analyticAt_zero _

end GapFamily.Analytic.CuspSchurLocal
