import GapFamily.Analytic.Cusp.Profile.CuspWeightedSchurGradient
import GapFamily.Analytic.Cusp.Profile.CuspWeightedSchurPhysical
import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedFramePhysical
import GapFamily.Analytic.Cusp.Schur.CuspSchurGradientExpansion

/-!
# Actual physical gradients of the weighted Schur response

These identities concern the closed gradient of the genuine weighted-source
Schur candidate before restricting the output height. No source support or
derivative of a sharp output cutoff is assumed.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurWeighted

open CuspSchurLocal ModularGradient

private theorem localGradientCoefficient_eq_physical {α : ℝ} (hα : 0 ≤ α)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) :
    (CuspSchur.continuedDenominator κ)⁻¹ * localNumerator α hα κ f =
      CuspSchur.schurNumerator (parameter κ) (cuspScalarPencilSolution (parameter κ))
        (cuspWeightedInput α hα f) / CuspSchur.actualSchurDenominator (parameter κ) := by
  have hd : CuspSchur.actualSchurDenominator (parameter κ) =
      CuspSchur.continuedDenominator κ := CuspSchur.actualSchurDenominator_eq_continued hκ
  have hn : localNumerator α hα κ f = CuspSchur.schurNumerator (parameter κ)
      (cuspScalarPencilSolution (parameter κ)) (cuspWeightedInput α hα f) := by
    rw [localNumerator_eq_physical hα hκ hp]
    simp only [CuspSchur.schurNumerator, CuspSchur.zeroTraceResponse_apply,
      map_add, inner_add_right, meanZeroCuspEmbedding_apply, scalarCuspEmbedding_apply]
  rw [hn, hd]
  simp only [div_eq_mul_inv, mul_comm]

/-- The horizontal output is the actual weighted-source closed gradient.
This channel needs no restriction on either auxiliary height. -/
theorem continuedLocalSchurGradientX_apply_eq_physical {α : ℝ} (hα : 0 ≤ α)
    (L T : ℝ) {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) :
    continuedLocalSchurGradientX α hα L T κ f = modularLowCut (Real.exp L)
      (formGradient (CuspSchur.actualSchurSolution (parameter κ)
        (cuspWeightedInput α hα f))).ofLp.1 := by
  change modularLowCut (Real.exp L)
      (constrainedGradientX κ (cuspWeightedInput α hα f)) +
      ((CuspSchur.continuedDenominator κ)⁻¹ * localNumerator α hα κ f) •
        (parameter κ • modularLowCut (Real.exp L)
          (constrainedGradientX κ modularConstant)) = _
  conv_rhs =>
    rw [actualSchurSolution_gradient_fst_expansion]
    rw [map_add, map_smul, map_smul]
  rw [localGradientCoefficient_eq_physical hα hκ hp]
  rfl

/-- The vertical output contains the genuine scalar weighted-source gradient
and the unchanged constant-response gradient. -/
theorem continuedLocalSchurGradientY_apply_eq_physical {α L T : ℝ}
    (hα : 0 < α) (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) :
    continuedLocalSchurGradientY α hα.le L T κ f = modularLowCut (Real.exp L)
      (formGradient (CuspSchur.actualSchurSolution (parameter κ)
        (cuspWeightedInput α hα.le f))).ofLp.2 := by
  change (modularLowCut (Real.exp L)
      (constrainedGradientY κ (cuspWeightedInput α hα.le f)) +
        cuspGreenWeightedFrameLocalOutput α hα.le L T κ (cuspHalfLineSourceCoefficient f)) +
      ((CuspSchur.continuedDenominator κ)⁻¹ * localNumerator α hα.le κ f) •
        (parameter κ • (modularLowCut (Real.exp L)
          (constrainedGradientY κ modularConstant) +
            cuspConstantLocalVerticalGradient L κ)) = _
  rw [cuspGreenWeightedFrameLocalOutput_eq_physical hα hL hT hLT hκ f,
    cuspConstantLocalVerticalGradient_eq_pencil_lowCut hL hκ]
  conv_rhs =>
    rw [actualSchurSolution_gradient_snd_expansion]
    rw [map_add, map_add, map_smul, map_smul, map_add]
  rw [localGradientCoefficient_eq_physical hα.le hκ hp]
  rfl

theorem continuedLocalSchurGradientX_eq_physical {α : ℝ} (hα : 0 ≤ α)
    (L T : ℝ) {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) :
    continuedLocalSchurGradientX α hα L T κ =
      ((modularLowCut (Real.exp L)).comp
        (((WithLp.fstL 2 ℂ ModularHilbert ModularHilbert).comp formGradient).comp
          (CuspSchur.actualSchurSolution (parameter κ)))).comp (cuspWeightedInput α hα) := by
  apply ContinuousLinearMap.ext
  intro f
  exact continuedLocalSchurGradientX_apply_eq_physical hα L T hκ hp f

theorem continuedLocalSchurGradientY_eq_physical {α L T : ℝ}
    (hα : 0 < α) (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) :
    continuedLocalSchurGradientY α hα.le L T κ =
      ((modularLowCut (Real.exp L)).comp
        (((WithLp.sndL 2 ℂ ModularHilbert ModularHilbert).comp formGradient).comp
          (CuspSchur.actualSchurSolution (parameter κ)))).comp (cuspWeightedInput α hα.le) := by
  apply ContinuousLinearMap.ext
  intro f
  exact continuedLocalSchurGradientY_apply_eq_physical hα hL hT hLT hκ hp f

end GapFamily.Analytic.CuspSchurWeighted
