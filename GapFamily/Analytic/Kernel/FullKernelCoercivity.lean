import GapFamily.Analytic.Kernel.FullKernelPropagation
import GapFamily.Analytic.Kernel.FullKernelObservation
import GapFamily.Analytic.Foundation.PositiveOperatorEnergy
import GapFamily.Analytic.Foundation.CoercivityEstimate

/-! Coercivity estimate for the actual kernel. Positivity of the enlarged physical
compression is an explicit premise at this layer. `FullKernelInverse`
discharges it using the proved spatial-energy bridge and kernel positivity. -/

noncomputable section

open Real

namespace GapFamily.Analytic

private theorem selfAdjoint_id_add {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) : IsSelfAdjoint (ContinuousLinearMap.id ℂ H + R) :=
  ContinuousLinearMap.isPositive_id.isSelfAdjoint.add hR

theorem isSelfAdjoint_correctedLowBandIdentityPlus {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (b : ℝ) : IsSelfAdjoint (correctedLowBandIdentityPlus J b) := by
  exact selfAdjoint_id_add _ (isSelfAdjoint_correctedLowBandOperator J b)

/-- Positivity descends through the actual isometric zero extension. -/
theorem isPositive_correctedLowBandIdentityPlus_of_extension
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b B : ℝ} (hbB : b ≤ B)
    (hP : (correctedLowBandIdentityPlus J B).IsPositive) :
    (correctedLowBandIdentityPlus J b).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨isSelfAdjoint_correctedLowBandIdentityPlus J b, ?_⟩
  intro f
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
  rw [← inner_correctedLowBandIdentityPlus_extension J hbB f f]
  exact hP.re_inner_nonneg_right _

/-- The enlarged response is controlled by the original quadratic energy. -/
theorem norm_correctedLowBandIdentityPlus_extension_le_energy
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b B : ℝ} (hbB : b ≤ B)
    (hP : (correctedLowBandIdentityPlus J B).IsPositive) (f : LowBandHilbert J b) :
    ‖correctedLowBandIdentityPlus J B (lowBandHilbertExtension J hbB f)‖ ≤
      sqrt ‖correctedLowBandIdentityPlus J B‖ *
        sqrt (inner ℂ f (correctedLowBandIdentityPlus J b f)).re := by
  have h := norm_sq_apply_le_norm_mul_energy (correctedLowBandIdentityPlus J B)
    hP (lowBandHilbertExtension J hbB f)
  rw [inner_correctedLowBandIdentityPlus_extension J hbB f f] at h
  rw [← sqrt_mul (norm_nonneg _)]
  exact (le_sqrt (norm_nonneg _) (mul_nonneg (norm_nonneg _)
    ((isPositive_correctedLowBandIdentityPlus_of_extension J hbB hP).re_inner_nonneg_right f))).mpr h

def correctedPropagationLoss {ι : Type*} [Fintype ι] (J : ι → ℤ) (b : ℝ) : ℝ :=
  20000 * (Fintype.card ι : ℝ) * b * exp (correctedPropagationExponent * b) *
    sqrt ‖correctedLowBandIdentityPlus J (4 * b)‖

theorem correctedPropagationLoss_nonneg {ι : Type*} [Fintype ι]
    (J : ι → ℤ) {b : ℝ} (hb : 0 ≤ b) : 0 ≤ correctedPropagationLoss J b := by
  unfold correctedPropagationLoss
  positivity

/-- The full low-band response satisfies the quarter-power energy estimate.
No inverse has been used, and the scalar channel is observed only if present. -/
theorem norm_sq_correctedLowBandOperator_le_energy
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (b : ℝ) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b)
    (hP : (correctedLowBandIdentityPlus J (4 * b)).IsPositive)
    (f : LowBandHilbert J b) :
    ‖correctedLowBandOperator J b f‖ ^ 2 ≤ correctedPropagationLoss J b * ‖f‖ *
      sqrt (inner ℂ f (correctedLowBandIdentityPlus J b f)).re := by
  have hbpos : 0 < b := by linarith
  have hbB : b ≤ 4 * b := by linarith
  have h := norm_sq_correctedLowBandOperator_le_of_observation J hJ b hb hband f
    (2 * ‖correctedLowBandIdentityPlus J (4 * b) (lowBandHilbertExtension J hbB f)‖)
    (by positivity)
    (fun i hi => sqrt_integral_norm_sq_correctedKernelScalarNormalizedResponse_le_identityPlus
      J hbpos f i hi)
    (fun i _ => sqrt_integral_norm_sq_correctedKernelScaledResponse_le_identityPlus
      J hbpos f i (hband i).le)
  apply h.trans
  calc
    _ ≤ 10000 * (Fintype.card ι : ℝ) * b *
        exp (correctedPropagationExponent * b) * ‖f‖ *
        (2 * (sqrt ‖correctedLowBandIdentityPlus J (4 * b)‖ *
          sqrt (inner ℂ f (correctedLowBandIdentityPlus J b f)).re)) := by
      gcongr
      exact norm_correctedLowBandIdentityPlus_extension_le_energy J hbB hP f
    _ = _ := by unfold correctedPropagationLoss; ring

/-- The explicit coefficient obtained from the proved response estimate. -/
def correctedLowBandCoercivityConstant {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (b : ℝ) : ℝ :=
  coercivityEstimateConstant ‖correctedLowBandIdentityPlus J b‖ (correctedPropagationLoss J b)

theorem correctedLowBandCoercivityConstant_pos {ι : Type*} [Fintype ι]
    (J : ι → ℤ) {b : ℝ} (hb : 0 ≤ b) :
    0 < correctedLowBandCoercivityConstant J b :=
  coercivityEstimateConstant_pos (norm_nonneg _) (correctedPropagationLoss_nonneg J hb)

/-- Quantitative coercivity follows from the actual enlarged-band positivity;
there is no assumed inverse or assumed unique continuation in this step. -/
theorem correctedLowBandIdentityPlus_coercive_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (b : ℝ) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b)
    (hP : (correctedLowBandIdentityPlus J (4 * b)).IsPositive)
    (f : LowBandHilbert J b) :
    correctedLowBandCoercivityConstant J b * ‖f‖ ^ 2 ≤
      (inner ℂ f (correctedLowBandIdentityPlus J b f)).re := by
  have hPb := isPositive_correctedLowBandIdentityPlus_of_extension J (by linarith) hP
  apply coercivityEstimateConstant_mul_sq_le_of_triangle (norm_nonneg _)
    (hPb.re_inner_nonneg_right f) (norm_nonneg _) (correctedPropagationLoss_nonneg J (by linarith))
  · calc
      ‖f‖ = ‖correctedLowBandIdentityPlus J b f - correctedLowBandOperator J b f‖ := by
        rw [correctedLowBandIdentityPlus_apply, add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  · exact norm_sq_apply_le_norm_mul_energy (correctedLowBandIdentityPlus J b) hPb f
  · exact norm_sq_correctedLowBandOperator_le_energy J hJ b hb hband hP f

theorem isUnit_correctedLowBandIdentityPlus_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (b : ℝ) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b)
    (hP : (correctedLowBandIdentityPlus J (4 * b)).IsPositive) :
    IsUnit (correctedLowBandIdentityPlus J b) :=
  CoerciveOperatorInverse.isUnit_of_coercive _
    (correctedLowBandCoercivityConstant_pos J (by linarith))
    (correctedLowBandIdentityPlus_coercive_of_positive J hJ b hb hband hP)

/-- The inverse is the actual inverse in the bounded-operator algebra. -/
def correctedLowBandInverse {ι : Type*} [Fintype ι] (J : ι → ℤ) (b : ℝ) :
    LowBandHilbert J b →L[ℂ] LowBandHilbert J b :=
  Ring.inverse (correctedLowBandIdentityPlus J b)

theorem correctedLowBandIdentityPlus_inverse_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (b : ℝ) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b)
    (hP : (correctedLowBandIdentityPlus J (4 * b)).IsPositive)
    (f : LowBandHilbert J b) :
    correctedLowBandIdentityPlus J b (correctedLowBandInverse J b f) = f :=
  CoerciveOperatorInverse.apply_inverse_of_coercive _
    (correctedLowBandCoercivityConstant_pos J (by linarith))
    (correctedLowBandIdentityPlus_coercive_of_positive J hJ b hb hband hP) f

theorem norm_correctedLowBandInverse_le_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (b : ℝ) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b)
    (hP : (correctedLowBandIdentityPlus J (4 * b)).IsPositive) :
    ‖correctedLowBandInverse J b‖ ≤ (correctedLowBandCoercivityConstant J b)⁻¹ :=
  CoerciveOperatorInverse.norm_inverse_le_of_coercive _
    (correctedLowBandCoercivityConstant_pos J (by linarith))
    (correctedLowBandIdentityPlus_coercive_of_positive J hJ b hb hband hP)

end GapFamily.Analytic
