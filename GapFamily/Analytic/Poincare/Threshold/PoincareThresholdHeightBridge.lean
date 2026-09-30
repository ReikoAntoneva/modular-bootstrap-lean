import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdScalarDecomposition
import GapFamily.Analytic.Cusp.Threshold.CuspThresholdHeightAbsorption
import GapFamily.Analytic.Cusp.Threshold.CuspThresholdHeightCoherence

noncomputable section
namespace GapFamily.Analytic.PoincareThresholdSchurValue
open Set Filter MeasureTheory UpperHalfPlane ModularGradient PoincareCanonical
  PoincareHighCusp CuspConstrainedThreshold CuspThresholdScalar
  CuspThresholdHeight UpperWeighted
open scoped ContDiff Topology

/-- The actual canonical threshold bridge can be realized at an absorption height
above any supplied chart height. The cutoff absorption remains an exact operator equality. -/
theorem exists_thresholdResidual_ae_explicit_value_of_lower_height
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U) (J : ℤ) (B : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ B ≤ L ∧
      (upperCutoffHilbertValueOperator χ hχ hc hs).comp (modularLowCut (Real.exp L)) =
        upperCutoffHilbertValueOperator χ hχ hc hs ∧
      (fun z => thresholdSeed J (ofComplex z) - continuedHighCusp J 0 z) =ᵐ[volume.restrict U]
        (upperCutoffHilbertValueOperator χ hχ hc hs
          (CuspSchurWeighted.continuedLocalSchur (1 / 4) (by norm_num) L L 0
            (cuspPoincareResidualSource J (1 / 4) (by norm_num) 0))) := by
  obtain ⟨L₀, hL₀, hAbs₀, hvalue⟩ :=
    exists_thresholdResidual_ae_explicit_value χ hχ hc hs U hU hχU J
  let L : ℝ := max L₀ B
  have hL : 0 ≤ L := hL₀.trans (le_max_left _ _)
  have hAbs := upperCutoffHilbertValueOperator_lowCut_mono hχ hc hs (le_max_left L₀ B) hAbs₀
  refine ⟨L, hL, le_max_right _ _, hAbs, ?_⟩
  have he := upperWeightedSchurValue_height_zero_eq χ hχ hc hs
    (by norm_num : (0 : ℝ) < 1 / 4) hL₀ hL hAbs₀ hAbs
  let F := cuspPoincareResidualSource J (1 / 4) (by norm_num) 0
  have hv := congrArg (fun T : ModularHilbert →L[ℂ] UpperField => T F) he
  change upperCutoffHilbertValueOperator χ hχ hc hs
      (CuspSchurWeighted.continuedLocalSchur (1 / 4) (by norm_num) L₀ L₀ 0 F) =
    upperCutoffHilbertValueOperator χ hχ hc hs
      (CuspSchurWeighted.continuedLocalSchur (1 / 4) (by norm_num) L L 0 F) at hv
  filter_upwards [hvalue] with z hz
  exact hz.trans (congrArg (fun f : UpperField => f z) hv)

/-- The same arbitrarily large actual absorption height retains the canonical
constrained-plus-scalar threshold decomposition, with the constrained low cutoff removed. -/
theorem exists_thresholdResidual_ae_constrained_scalar_of_lower_height
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U) (J : ℤ) (B : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ B ≤ L ∧
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
  obtain ⟨L, hL, hBL, hAbs, hvalue⟩ :=
    exists_thresholdResidual_ae_explicit_value_of_lower_height χ hχ hc hs U hU hχU J B
  refine ⟨L, hL, hBL, hAbs, ?_⟩
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
