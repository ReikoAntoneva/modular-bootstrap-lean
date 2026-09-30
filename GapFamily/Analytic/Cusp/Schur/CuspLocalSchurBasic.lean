import GapFamily.Analytic.Cusp.Scalar.CuspConstantLocalResponse
import GapFamily.Analytic.Cusp.Scalar.CuspConstantPairingContinuation
import GapFamily.Analytic.Cusp.Green.CuspGreenBoundedOutput
import GapFamily.Analytic.Cusp.Schur.CuspSchurThreshold

/-!
# The actual finite-height Schur family

The source and output height cutoffs are placed explicitly. The scalar
numerator and correction vector use the proved local Green and constant
responses; the denominator retains its actual global normalization.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal
open ModularGradient

def parameter (κ : ℂ) : ℂ := 1 / 4 - κ ^ 2

def constrainedResponse (κ : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  meanZeroCuspEmbedding.comp (cuspMeanZeroPencilSolution (parameter κ))

def localZeroTrace (L T : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  ((modularLowCut (Real.exp L)).comp (constrainedResponse κ)).comp
    (modularLowCut (Real.exp T)) + cuspGreenLocalizedOutput L T κ

def localNumerator (T : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] ℂ :=
  (innerSL ℂ modularConstant + parameter κ •
    ((innerSL ℂ modularConstant).comp (constrainedResponse κ) +
      cuspConstantPairingFunctional T κ)).comp (modularLowCut (Real.exp T))

def localTraceVector (L : ℝ) (κ : ℂ) : ModularHilbert :=
  modularLowCut (Real.exp L) modularConstant + parameter κ •
    (modularLowCut (Real.exp L) (constrainedResponse κ modularConstant) +
      cuspConstantLocalResponse L κ)

/-- Actual finite-height operator continuation. No global form vector is used at threshold. -/
def continuedLocalSchur (L T : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  localZeroTrace L T κ +
    ((CuspSchur.continuedDenominator κ)⁻¹ • localNumerator T κ).smulRight
      (localTraceVector L κ)

end GapFamily.Analytic.CuspSchurLocal
