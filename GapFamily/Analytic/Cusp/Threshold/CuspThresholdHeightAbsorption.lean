import GapFamily.Analytic.Foundation.UpperCutoffCommonHeight

noncomputable section
namespace GapFamily.Analytic.CuspThresholdHeight
open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

/-- Once an actual compact upper cutoff absorbs a logarithmic height truncation,
it absorbs every larger one. -/
theorem upperCutoffHilbertValueOperator_lowCut_mono {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) {L₁ L₂ : ℝ} (hL : L₁ ≤ L₂)
    (habs : (upperCutoffHilbertValueOperator χ hχ hc hs).comp
      (modularLowCut (Real.exp L₁)) = upperCutoffHilbertValueOperator χ hχ hc hs) :
    (upperCutoffHilbertValueOperator χ hχ hc hs).comp (modularLowCut (Real.exp L₂)) =
      upperCutoffHilbertValueOperator χ hχ hc hs := by
  have hheight : Real.exp L₁ ≤ Real.exp L₂ := Real.exp_le_exp.mpr hL
  have hf (f : ModularHilbert) :
      upperCutoffHilbertValueOperator χ hχ hc hs (modularLowCut (Real.exp L₁) f) =
        upperCutoffHilbertValueOperator χ hχ hc hs f :=
    congrArg (fun T : ModularHilbert →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) => T f) habs
  apply ContinuousLinearMap.ext
  intro f
  change upperCutoffHilbertValueOperator χ hχ hc hs (modularLowCut (Real.exp L₂) f) = _
  rw [← hf (modularLowCut (Real.exp L₂) f),
    WeightedSeam.modularLowCut_lowCut_of_le_rev hheight, hf]

/-- An actual absorbing height can be chosen above any prescribed real lower bound. -/
theorem exists_upperCutoffHilbertValueOperator_lowCut_ge {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (B : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ B ≤ L ∧
      (upperCutoffHilbertValueOperator χ hχ hc hs).comp (modularLowCut (Real.exp L)) =
        upperCutoffHilbertValueOperator χ hχ hc hs := by
  obtain ⟨L₀, hL₀, habs⟩ := exists_upperCutoffHilbertValueOperator_lowCut hχ hc hs
  refine ⟨max L₀ B, hL₀.trans (le_max_left L₀ B), le_max_right L₀ B, ?_⟩
  exact upperCutoffHilbertValueOperator_lowCut_mono hχ hc hs (le_max_left L₀ B) habs

end GapFamily.Analytic.CuspThresholdHeight
