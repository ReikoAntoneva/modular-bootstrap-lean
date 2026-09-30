import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurGradient
import GapFamily.Analytic.Cusp.Schur.CuspSchurGradientExpansion
import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurPhysical

/-!
# Physical identification of the continued local Schur gradients

The output cut is applied to the actual closed gradient of the original
form-domain Schur candidate. It is not differentiated. The identities are
physical-half-plane identities of the literal totalized candidates and do not
assert an inverse at a singular parameter.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal
open ModularGradient

private theorem localGradientCoefficient_eq_physical {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (f : ModularHilbert) :
    (CuspSchur.continuedDenominator κ)⁻¹ * localNumerator T κ f =
      CuspSchur.schurNumerator (parameter κ) (cuspScalarPencilSolution (parameter κ))
        (modularLowCut (Real.exp T) f) / CuspSchur.actualSchurDenominator (parameter κ) := by
  have hd : CuspSchur.actualSchurDenominator (parameter κ) =
      CuspSchur.continuedDenominator κ := CuspSchur.actualSchurDenominator_eq_continued hκ
  have hn : localNumerator T κ f = CuspSchur.schurNumerator (parameter κ)
      (cuspScalarPencilSolution (parameter κ)) (modularLowCut (Real.exp T) f) := by
    rw [localNumerator_eq_physical hT hκ]
    simp only [CuspSchur.schurNumerator, CuspSchur.zeroTraceResponse_apply,
      map_add, inner_add_right, meanZeroCuspEmbedding_apply, scalarCuspEmbedding_apply]
  rw [hn, hd]
  simp only [div_eq_mul_inv, mul_comm]

/-- The horizontal field is the output restriction of the original actual gradient.
This channel allows arbitrary output height L. -/
theorem continuedLocalSchurGradientX_apply_eq_physical (L : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (f : ModularHilbert) :
    continuedLocalSchurGradientX L T κ f = modularLowCut (Real.exp L)
      (formGradient (CuspSchur.actualSchurSolution (parameter κ)
        (modularLowCut (Real.exp T) f))).ofLp.1 := by
  change modularLowCut (Real.exp L)
      (constrainedGradientX κ (modularLowCut (Real.exp T) f)) +
      ((CuspSchur.continuedDenominator κ)⁻¹ * localNumerator T κ f) •
        (parameter κ • modularLowCut (Real.exp L)
          (constrainedGradientX κ modularConstant)) = _
  conv_rhs =>
    rw [actualSchurSolution_gradient_fst_expansion]
    rw [map_add, map_smul, map_smul]
  rw [localGradientCoefficient_eq_physical hT hκ]
  rfl

/-- The vertical field includes the physical scalar Green gradient and the
physical constant-response gradient before applying the output restriction. -/
theorem continuedLocalSchurGradientY_apply_eq_physical {L T : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) {κ : ℂ} (hκ : 0 < κ.re) (f : ModularHilbert) :
    continuedLocalSchurGradientY L T κ f = modularLowCut (Real.exp L)
      (formGradient (CuspSchur.actualSchurSolution (parameter κ)
        (modularLowCut (Real.exp T) f))).ofLp.2 := by
  change (modularLowCut (Real.exp L)
      (constrainedGradientY κ (modularLowCut (Real.exp T) f)) +
        cuspGreenFrameBoundedOutput L T κ (modularLowCut (Real.exp T) f)) +
      ((CuspSchur.continuedDenominator κ)⁻¹ * localNumerator T κ f) •
        (parameter κ • (modularLowCut (Real.exp L)
          (constrainedGradientY κ modularConstant) +
            cuspConstantLocalVerticalGradient L κ)) = _
  rw [cuspGreenFrameBoundedOutput_eq_physical hL hT hκ
      (modularLowCut (Real.exp T) f) (modularHighCut_lowCut (Real.exp T) f),
    cuspConstantLocalVerticalGradient_eq_pencil_lowCut hL hκ]
  conv_rhs =>
    rw [actualSchurSolution_gradient_snd_expansion]
    rw [map_add, map_add, map_smul, map_smul, map_add]
  rw [localGradientCoefficient_eq_physical hT hκ]
  rfl

/-- Equality of bounded horizontal source-to-output maps on the physical half-plane. -/
theorem continuedLocalSchurGradientX_eq_physical (L : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) :
    continuedLocalSchurGradientX L T κ =
      ((modularLowCut (Real.exp L)).comp
        (((WithLp.fstL 2 ℂ ModularHilbert ModularHilbert).comp formGradient).comp
          (CuspSchur.actualSchurSolution (parameter κ)))).comp
            (modularLowCut (Real.exp T)) := by
  apply ContinuousLinearMap.ext
  intro f
  exact continuedLocalSchurGradientX_apply_eq_physical L hT hκ f

/-- Equality of bounded vertical source-to-output maps on the physical half-plane. -/
theorem continuedLocalSchurGradientY_eq_physical {L T : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) {κ : ℂ} (hκ : 0 < κ.re) :
    continuedLocalSchurGradientY L T κ =
      ((modularLowCut (Real.exp L)).comp
        (((WithLp.sndL 2 ℂ ModularHilbert ModularHilbert).comp formGradient).comp
          (CuspSchur.actualSchurSolution (parameter κ)))).comp
            (modularLowCut (Real.exp T)) := by
  apply ContinuousLinearMap.ext
  intro f
  exact continuedLocalSchurGradientY_apply_eq_physical hL hT hκ f

end GapFamily.Analytic.CuspSchurLocal
