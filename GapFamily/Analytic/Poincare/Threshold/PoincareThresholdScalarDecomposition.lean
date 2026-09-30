import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdSchurValue
import GapFamily.Analytic.Cusp.Threshold.CuspThresholdScalarBound

/-! The actual canonical threshold seed is connected to the proved scalar Schur component. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdSchurValue
open Set MeasureTheory UpperHalfPlane ModularGradient PoincareCanonical
  PoincareHighCusp CuspConstrainedThreshold CuspThresholdScalar
open scoped ContDiff

/-- The canonical full threshold residual is the actual constrained plus scalar
Schur field on every upper cutoff plateau. The scalar summand is precisely the
operator whose literal cusp profile and uniform square-root bound were proved;
the constrained summand is retained, with no pointwise growth assumption. -/
theorem exists_thresholdResidual_ae_constrained_scalar
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U) (J : ℤ) :
    ∃ L : ℝ, 0 ≤ L ∧
      (upperCutoffHilbertValueOperator χ hχ hc hs).comp (modularLowCut (Real.exp L)) =
        upperCutoffHilbertValueOperator χ hχ hc hs ∧
      (fun z => thresholdSeed J (ofComplex z) - continuedHighCusp J 0 z) =ᵐ[volume.restrict U]
        (fun z =>
          upperCutoffHilbertValueOperator χ hχ hc hs
            (meanZeroCuspEmbedding
              (constrainedForm (1 / 4) (by norm_num)
                (cuspPoincareResidualSource J (1 / 4) (by norm_num) 0))) z +
          upperCutoffHilbertValueOperator χ hχ hc hs
            (scalarLocalOutput (1 / 4) (by norm_num) L L
              (cuspPoincareResidualSource J (1 / 4) (by norm_num) 0)) z) := by
  obtain ⟨L, hL, hAbs, hvalue⟩ := exists_thresholdResidual_ae_explicit_value χ hχ hc hs U hU hχU J
  refine ⟨L, hL, hAbs, ?_⟩
  let F := cuspPoincareResidualSource J (1 / 4) (by norm_num) 0
  let C := modularLowCut (Real.exp L)
    (meanZeroCuspEmbedding (constrainedForm (1 / 4) (by norm_num) F))
  let S := scalarLocalOutput (1 / 4) (by norm_num) L L F
  have he : CuspSchurWeighted.continuedLocalSchur (1 / 4) (by norm_num) L L 0 F = C + S :=
    continuedLocalSchur_eq_constrained_add_scalar (1 / 4) (by norm_num) L L F
  let P := upperCutoffHilbertValueOperator χ hχ hc hs
  let V := meanZeroCuspEmbedding (constrainedForm (1 / 4) (by norm_num) F)
  have hPC : P C = P V := congrArg (fun T : ModularHilbert →L[ℂ] LocalPoisson.Field => T V) hAbs
  have hadd := ae_restrict_of_ae (s := U) (Lp.coeFn_add (P C) (P S))
  filter_upwards [hvalue, hadd] with z hz ha
  change _ = P V z + P S z
  change _ = P (CuspSchurWeighted.continuedLocalSchur (1 / 4) (by norm_num) L L 0 F) z at hz
  rw [hz, he, map_add, ha, Pi.add_apply, hPC]

end GapFamily.Analytic.PoincareThresholdSchurValue
