import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurGradient
import GapFamily.Analytic.Modular.Geometry.ModularCutoffHeight

/-!
# Analytic cutoff value and Laplacian families

Actual compact coefficient multipliers turn the continued finite-height value
and gradient responses into bounded operators analytic through threshold.
The second family uses the physical cutoff commutator's exact coefficients;
physical operator-domain membership is a separate statement.
-/

noncomputable section

namespace GapFamily.Analytic.CuspSchurLocal

open ModularGradient.InteriorCutoff
open scoped ContDiff

/-- The continued local Schur response multiplied by the actual smooth cutoff. -/
def continuedCutoffSchur (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (L T : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  (valueMultiplier χ hχ hc).comp (continuedLocalSchur L T κ)

/-- The bounded candidate Laplacian family with the actual source projection,
spectral parameter, and first/second cutoff derivative coefficients. -/
def continuedCutoffLaplacian (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (L T : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  (valueMultiplier χ hχ hc).comp (modularLowCut (Real.exp T)) +
    parameter κ • continuedCutoffSchur χ hχ hc L T κ +
    (secondMultiplier χ hχ hc 1 + secondMultiplier χ hχ hc Complex.I).comp
      (continuedLocalSchur L T κ) -
    (2 : ℂ) •
      ((derivativeMultiplier χ hχ hc 1).comp (continuedLocalSchurGradientX L T κ) +
        (derivativeMultiplier χ hχ hc Complex.I).comp
          (continuedLocalSchurGradientY L T κ))

private theorem analyticAt_postcompose
    (A : ModularHilbert →L[ℂ] ModularHilbert)
    {F : ℂ → (ModularHilbert →L[ℂ] ModularHilbert)} (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (fun κ => A.comp (F κ)) 0 :=
  ((ContinuousLinearMap.compL ℂ ModularHilbert ModularHilbert ModularHilbert A).analyticAt
    (F 0)).comp hF

/-- Operator-norm analyticity of the genuine bounded cutoff value family. -/
theorem continuedCutoffSchur_analyticAt_zero (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (L T : ℝ) :
    AnalyticAt ℂ (continuedCutoffSchur χ hχ hc L T) 0 :=
  analyticAt_postcompose _ (continuedLocalSchur_analyticAt_zero L T)

/-- Operator-norm analyticity of the bounded cutoff Laplacian candidate family;
no support-in-the-interior or physical-domain premise is needed here. -/
theorem continuedCutoffLaplacian_analyticAt_zero (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (L T : ℝ) :
    AnalyticAt ℂ (continuedCutoffLaplacian χ hχ hc L T) 0 := by
  exact ((analyticAt_const.add ((parameter_analyticAt 0).smul
    (continuedCutoffSchur_analyticAt_zero χ hχ hc L T))).add
      (analyticAt_postcompose _ (continuedLocalSchur_analyticAt_zero L T))).sub
    ((analyticAt_const (v := (2 : ℂ))).smul
      ((analyticAt_postcompose (derivativeMultiplier χ hχ hc 1)
        (continuedLocalSchurGradientX_analyticAt_zero L T)).add
        (analyticAt_postcompose (derivativeMultiplier χ hχ hc Complex.I)
          (continuedLocalSchurGradientY_analyticAt_zero L T))))

end GapFamily.Analytic.CuspSchurLocal
