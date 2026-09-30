import GapFamily.Analytic.Cusp.Schur.CuspSchurDenominator
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroPencilAnalytic

/-!
# Local analyticity of the scalar continued denominator

The actual constrained response is analytic at every unit of its pencil.
Evaluation at the constant source, the genuine ambient embedding, and pairing
with the constant are bounded complex-linear maps. Their composition proves
analyticity of the scalar denominator, including at threshold under the explicit
quarter-unit hypothesis. The displayed quarter-pairing positivity premise then
gives nonvanishing in a neighborhood of threshold.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchur

open Filter
open scoped Topology ComplexOrder

/-- Only regularity of the actual constrained pencil is needed for scalar analyticity. -/
theorem continuedDenominator_analyticAt {κ : ℂ}
    (hunit : IsUnit (cuspMeanZeroPencil ((1 / 4 : ℂ) - κ ^ 2))) :
    AnalyticAt ℂ continuedDenominator κ := by
  let L : (ModularHilbert →L[ℂ] cuspMeanZeroForm) →L[ℂ] ℂ :=
    (innerSL ℂ modularConstant).comp
      (meanZeroCuspEmbedding.comp
        (ContinuousLinearMap.apply ℂ cuspMeanZeroForm modularConstant))
  have hs : AnalyticAt ℂ (fun k : ℂ => (1 / 4 : ℂ) - k ^ 2) κ := by fun_prop
  have hS : AnalyticAt ℂ
      (fun k : ℂ => cuspMeanZeroPencilSolution ((1 / 4 : ℂ) - k ^ 2)) κ :=
    (cuspMeanZeroPencilSolution_analyticAt hunit).comp_of_eq hs rfl
  have hL : AnalyticAt ℂ L (cuspMeanZeroPencilSolution ((1 / 4 : ℂ) - κ ^ 2)) :=
    ContinuousLinearMap.analyticAt (𝕜 := ℂ)
      (E := ModularHilbert →L[ℂ] cuspMeanZeroForm) (F := ℂ) L _
  have hL_apply (A : ModularHilbert →L[ℂ] cuspMeanZeroForm) :
      L A = inner ℂ modularConstant (meanZeroCuspEmbedding (A modularConstant)) := rfl
  have hm : AnalyticAt ℂ (fun k : ℂ => inner ℂ modularConstant
      (meanZeroCuspEmbedding
        (cuspMeanZeroPencilSolution ((1 / 4 : ℂ) - k ^ 2) modularConstant))) κ := by
    simpa only [Function.comp_def, hL_apply] using hL.comp_of_eq hS rfl
  unfold continuedDenominator
  fun_prop

/-- Scalar threshold analyticity retains the actual quarter-unit premise. -/
theorem continuedDenominator_analyticAt_zero
    (hunit : IsUnit (cuspMeanZeroPencil (1 / 4 : ℂ))) :
    AnalyticAt ℂ continuedDenominator 0 := by
  apply continuedDenominator_analyticAt
  simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using hunit

/-- Actual quarter regularity and the stated pairing positivity give local scalar nonvanishing. -/
theorem continuedDenominator_eventually_ne_zero
    (hunit : IsUnit (cuspMeanZeroPencil (1 / 4 : ℂ)))
    (hV : 0 ≤ inner ℂ modularConstant
      (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) modularConstant))) :
    ∀ᶠ κ in 𝓝 (0 : ℂ), continuedDenominator κ ≠ 0 :=
  (continuedDenominator_analyticAt_zero hunit).continuousAt.eventually_ne
    (continuedDenominator_zero_ne_zero hV)

end GapFamily.Analytic.CuspSchur
