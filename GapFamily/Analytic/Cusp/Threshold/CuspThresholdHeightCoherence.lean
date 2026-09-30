import GapFamily.Analytic.Foundation.UpperWeightedSchurField
import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurCoherence

noncomputable section
namespace GapFamily.Analytic.CuspThresholdHeight
open Set Filter MeasureTheory UpperHalfPlane ModularGradient UpperWeighted
open scoped Topology ContDiff

/-- Two actual absorption heights give the same analytic upper-value germ, because
both equal the same physical weighted Schur value on a positive-real-part half-neighborhood. -/
theorem upperWeightedSchurValue_height_eventuallyEq
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) {α L₁ L₂ : ℝ}
    (hα : 0 < α) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hAbs₁ : (upperCutoffHilbertValueOperator χ hχ hc hs).comp
      (modularLowCut (Real.exp L₁)) = upperCutoffHilbertValueOperator χ hχ hc hs)
    (hAbs₂ : (upperCutoffHilbertValueOperator χ hχ hc hs).comp
      (modularLowCut (Real.exp L₂)) = upperCutoffHilbertValueOperator χ hχ hc hs) :
    upperWeightedSchurValue χ hχ hc hs α hα.le L₁ =ᶠ[𝓝 (0 : ℂ)]
      upperWeightedSchurValue χ hχ hc hs α hα.le L₂ := by
  apply CuspSchurCoherence.analyticAt_eventuallyEq_of_physical
    (upperWeightedSchurValue_analyticAt_zero χ hχ hc hs hα L₁)
    (upperWeightedSchurValue_analyticAt_zero χ hχ hc hs hα L₂)
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro κ hn hκ
  have hp : κ ≠ (1 / 2 : ℂ) := by
    intro he
    rw [he] at hn
    norm_num at hn
  apply ContinuousLinearMap.ext
  intro f
  exact (upperWeightedSchurValue_eq_physical χ hχ hc hs hα hL₁ hAbs₁ hκ hp f).trans
    (upperWeightedSchurValue_eq_physical χ hχ hc hs hα hL₂ hAbs₂ hκ hp f).symm

/-- In particular the literal threshold upper-value operator is independent of the
chosen nonnegative absorption height. -/
theorem upperWeightedSchurValue_height_zero_eq
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) {α L₁ L₂ : ℝ}
    (hα : 0 < α) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hAbs₁ : (upperCutoffHilbertValueOperator χ hχ hc hs).comp
      (modularLowCut (Real.exp L₁)) = upperCutoffHilbertValueOperator χ hχ hc hs)
    (hAbs₂ : (upperCutoffHilbertValueOperator χ hχ hc hs).comp
      (modularLowCut (Real.exp L₂)) = upperCutoffHilbertValueOperator χ hχ hc hs) :
    upperWeightedSchurValue χ hχ hc hs α hα.le L₁ 0 =
      upperWeightedSchurValue χ hχ hc hs α hα.le L₂ 0 :=
  (upperWeightedSchurValue_height_eventuallyEq χ hχ hc hs hα hL₁ hL₂ hAbs₁ hAbs₂).self_of_nhds

end GapFamily.Analytic.CuspThresholdHeight
