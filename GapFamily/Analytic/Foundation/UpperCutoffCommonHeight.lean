import GapFamily.Analytic.Modular.Elliptic.ModularUpperValueHeight
import GapFamily.Analytic.Modular.Elliptic.ModularUpperGradientRecovery

/-! A common finite height for the actual compact upper cutoff value and gradients. -/
noncomputable section
namespace GapFamily.Analytic.WeightedSeam
open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

theorem modularLowCut_lowCut_of_le_rev {H₁ H₂ : ℝ} (hH : H₁ ≤ H₂)
    (f : ModularHilbert) :
    modularLowCut H₁ (modularLowCut H₂ f) = modularLowCut H₁ f := by
  apply Lp.ext
  filter_upwards [modularLowCut_ae H₁ (modularLowCut H₂ f),
    modularLowCut_ae H₂ f, modularLowCut_ae H₁ f] with τ h₁₂ h₂ h₁
  rw [h₁₂, h₁]
  by_cases hτ : τ.im ≤ H₁
  · simp [hτ, h₂, hτ.trans hH]
  · simp [hτ]

theorem modularLowCut_comp_of_le_rev {H₁ H₂ : ℝ} (hH : H₁ ≤ H₂) :
    (modularLowCut H₁).comp (modularLowCut H₂) = modularLowCut H₁ := by
  apply ContinuousLinearMap.ext
  exact modularLowCut_lowCut_of_le_rev hH

theorem gradientLowCut_lowCut_of_le_rev {H₁ H₂ : ℝ} (hH : H₁ ≤ H₂)
    (g : GradientSpace) :
    gradientLowCut H₁ (gradientLowCut H₂ g) = gradientLowCut H₁ g := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact modularLowCut_lowCut_of_le_rev hH (WithLp.ofLp g).1
  · exact modularLowCut_lowCut_of_le_rev hH (WithLp.ofLp g).2

theorem gradientLowCut_comp_of_le_rev {H₁ H₂ : ℝ} (hH : H₁ ≤ H₂) :
    (gradientLowCut H₁).comp (gradientLowCut H₂) = gradientLowCut H₁ := by
  apply ContinuousLinearMap.ext
  exact gradientLowCut_lowCut_of_le_rev hH

/-- Enlarging to the maximum of the genuine value and gradient heights keeps
the value operator unchanged and recovers both actual cutoff derivatives. -/
theorem exists_upperCutoff_common_height (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∃ Bx By : GradientSpace →L[ℂ] Lp ℂ 2 (volume : Measure ℂ),
        (upperCutoffHilbertValueOperator χ hχ hc hs).comp (modularLowCut (Real.exp L)) =
          upperCutoffHilbertValueOperator χ hχ hc hs ∧
        Bx.comp ((gradientLowCut (Real.exp L)).comp formGradient) =
          upperCutoffGradientOperator χ hχ hc hs 1 ∧
        By.comp ((gradientLowCut (Real.exp L)).comp formGradient) =
          upperCutoffGradientOperator χ hχ hc hs Complex.I := by
  obtain ⟨Lm, hLm, hm⟩ := exists_upperCutoffHilbertValueOperator_lowCut hχ hc hs
  obtain ⟨Lg, _, hg⟩ := exists_upperCutoffGradient_recovery χ hχ hc hs
  obtain ⟨Bx, hx⟩ := hg 1
  obtain ⟨By, hy⟩ := hg Complex.I
  have hmle : Real.exp Lm ≤ Real.exp (max Lm Lg) :=
    Real.exp_le_exp.mpr (le_max_left Lm Lg)
  have hgle : Real.exp Lg ≤ Real.exp (max Lm Lg) :=
    Real.exp_le_exp.mpr (le_max_right Lm Lg)
  refine ⟨max Lm Lg, hLm.trans (le_max_left Lm Lg),
    Bx.comp (gradientLowCut (Real.exp Lg)),
    By.comp (gradientLowCut (Real.exp Lg)), ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro f
    have hmf (f : ModularHilbert) :
        upperCutoffHilbertValueOperator χ hχ hc hs (modularLowCut (Real.exp Lm) f) =
          upperCutoffHilbertValueOperator χ hχ hc hs f :=
      congrArg (fun T : ModularHilbert →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) => T f) hm
    change upperCutoffHilbertValueOperator χ hχ hc hs
      (modularLowCut (Real.exp (max Lm Lg)) f) = _
    rw [← hmf (modularLowCut (Real.exp (max Lm Lg)) f),
      modularLowCut_lowCut_of_le_rev hmle, hmf]
  · apply ContinuousLinearMap.ext
    intro u
    change Bx (gradientLowCut (Real.exp Lg)
      (gradientLowCut (Real.exp (max Lm Lg)) (formGradient u))) = _
    rw [gradientLowCut_lowCut_of_le_rev hgle]
    exact congrArg (fun T : FormDomain →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) => T u) hx
  · apply ContinuousLinearMap.ext
    intro u
    change By (gradientLowCut (Real.exp Lg)
      (gradientLowCut (Real.exp (max Lm Lg)) (formGradient u))) = _
    rw [gradientLowCut_lowCut_of_le_rev hgle]
    exact congrArg (fun T : FormDomain →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) => T u) hy

end GapFamily.Analytic.WeightedSeam
