import GapFamily.Analytic.Modular.Elliptic.ModularUpperGradientRecoveryBound
import GapFamily.Analytic.Foundation.HilbertRangeFactor

/-!
# Recovering actual upper-chart gradients from bounded-height modular data

The operator is constructed by factoring the actual cutoff gradient through
the actual truncated modular gradient, then extending on its Hilbert range.
It applies to all ambient gradient pairs, with exact recovery on every genuine
completed form-domain gradient. It assumes no compatibility oracle.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- One finite logarithmic height suffices to recover every ordinary derivative
direction of the actual compact upper cutoff, including across modular seams. -/
theorem exists_upperCutoffGradient_recovery (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ v : ℂ,
      ∃ B : GradientSpace →L[ℂ] Lp ℂ 2 (volume : Measure ℂ),
        B.comp ((gradientLowCut (Real.exp L)).comp formGradient) =
          upperCutoffGradientOperator χ hχ hc hs v := by
  obtain ⟨H, hH, hbound⟩ := exists_upperCutoffGradientOperator_lowCut_bound hχ hc hs
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  refine ⟨Real.log H, Real.log_nonneg hH, fun v => ?_⟩
  rw [Real.exp_log hHp]
  obtain ⟨C, _, hC⟩ := hbound v
  exact exists_hilbert_factor_of_norm_bound
    (upperCutoffGradientOperator χ hχ hc hs v)
    ((gradientLowCut H).comp formGradient) ⟨C, hC⟩

/-- An explicit pointwise version for the two physical coordinate directions.
The maps act on the Hilbert sum of arbitrary ambient modular L² pairs. -/
theorem exists_upperCutoffGradient_pair_recovery (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∃ Bx By : GradientSpace →L[ℂ] Lp ℂ 2 (volume : Measure ℂ),
        ∀ u : FormDomain,
          Bx (WithLp.toLp 2
            (modularLowCut (Real.exp L) (formGradient u).fst,
             modularLowCut (Real.exp L) (formGradient u).snd)) =
            upperCutoffGradientOperator χ hχ hc hs 1 u ∧
          By (WithLp.toLp 2
            (modularLowCut (Real.exp L) (formGradient u).fst,
             modularLowCut (Real.exp L) (formGradient u).snd)) =
            upperCutoffGradientOperator χ hχ hc hs Complex.I u := by
  obtain ⟨L, hL, hB⟩ := exists_upperCutoffGradient_recovery χ hχ hc hs
  obtain ⟨Bx, hBx⟩ := hB 1
  obtain ⟨By, hBy⟩ := hB Complex.I
  refine ⟨L, hL, Bx, By, fun u => ?_⟩
  constructor
  · exact congrArg (fun T : FormDomain →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) => T u) hBx
  · exact congrArg (fun T : FormDomain →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) => T u) hBy

end GapFamily.Analytic.ModularGradient
