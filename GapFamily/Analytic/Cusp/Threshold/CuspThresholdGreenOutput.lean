import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedLocal
import GapFamily.Analytic.Cusp.Green.CuspGreenCollarOutput

/-! The actual weighted threshold Green output is its literal min-kernel lift. -/
noncomputable section
namespace GapFamily.Analytic.CuspThresholdGreenOutput
open Set MeasureTheory CuspHalfLineLaplace

/-- The actual modular output at threshold agrees almost everywhere with the
square-root lift of the weighted min-kernel integral on its finite output window. -/
theorem cuspGreenWeightedLocalOutput_zero_ae {α L T : ℝ} (hα : 0 < α)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T) (f : HalfLineL2) :
    cuspGreenWeightedLocalOutput α hα.le L T 0 f =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im ∧ τ.im ≤ Real.exp L then
        Real.sqrt τ.im • (∫ u : ℝ in Ioi 0,
          ((min (Real.log τ.im) u : ℝ) : ℂ) * Complex.exp (-(α : ℂ) * u) * f u)
        else 0) := by
  change cuspGreenSourceEmbedding L
    (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ
      (cuspGreenWeightedLocalOperator α hα.le L T 0 f)) =ᵐ[modularMeasure] _
  refine cuspGreenSourceEmbedding_toLp_ae L hL
    (cuspGreenWeightedLocalOperator α hα.le L T 0 f)
    (fun t => ∫ u : ℝ in Ioi 0,
      ((min t u : ℝ) : ℂ) * Complex.exp (-(α : ℂ) * u) * f u) ?_
  intro t
  simpa only [cuspGreen_zero, sub_zero] using
    cuspGreenWeightedLocalOperator_apply hα.le hT hLT
      (by simpa using hα : 0 < ((α : ℂ) + 0).re) f t

end GapFamily.Analytic.CuspThresholdGreenOutput
