import GapFamily.Analytic.Kernel.FullKernelScalarAnchorResponse
import GapFamily.Analytic.Kernel.FullKernelInverseSignedMeasure
import GapFamily.Analytic.Kernel.FullKernelScalarColumnSuperposition
import GapFamily.Analytic.Kernel.FullKernelScalarColumnMass
import GapFamily.Analytic.Foundation.SignedIntegralContinuousLinearMap

/-! The actual repaired scalar seed pairs with the actual scalar response.
All ordinary masses are obtained from integrable densities, while only the
smoothing correction is passed through the Hilbert inverse. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace GapFamily.Analytic
open PoincareScalarFourier

/-- Weighted inverse mass is the real part of the ordinary input mass minus
its bounded smoothing correction. No Hilbert-space mass functional is used. -/
theorem correctedLowBandInverseSignedMeasure_threshold_eq
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B))
    (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) :
    (∑ i, (scalarThresholdCoefficient (J i)).re *
      correctedLowBandInverseSignedMeasure J B hB hunit f hf i univ) =
      ((∑ i, scalarThresholdCoefficient (J i) * ∫ e, f i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) -
        correctedSmoothingThresholdFunctional J B hB
          (Ring.inverse (correctedLowBandIdentityPlus J B) f)).re := by
  rw [correctedSmoothingThresholdFunctional_apply, ← Finset.sum_sub_distrib]
  conv_rhs => rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply, Complex.sub_re, Complex.mul_re,
    scalarThresholdCoefficient_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [correctedLowBandInverseSignedMeasure_apply_eq_sub J B hB hunit f hf i
    univ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hfre := (Complex.reCLM.integral_comp_comm (hf i)).symm
  have hrre := (Complex.reCLM.integral_comp_comm
    (correctedKernelResponse_integrable_lowBand J B hB
      (Ring.inverse (correctedLowBandIdentityPlus J B) f) (J i))).symm
  simp only [Complex.reCLM_apply] at hfre hrre
  rw [hfre, hrre]
  ring

/-- The threshold of a scalar signed seed repaired by the actual inverse is
its ordinary signed pairing with the actual physical scalar response. -/
theorem scalarAnchorResponsePhysical_signedIntegral
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 < B)
    (ν : SignedMeasure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, |(0 : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) :
    -ν univ - ∑ i, (scalarThresholdCoefficient (J i)).re *
      correctedSignedInverseMeasure (fun _ : Unit => ν) (fun _ => 0) J M B hM hB.le
        (fun _ => by simpa using hs) hunit i univ =
      ∫ᵛ E, scalarAnchorResponsePhysical J B hB.le E ∂<•ν := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have hs' : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M := by simpa using hs
  let f := correctedSignedResponseHilbert (fun _ : Unit => ν) (fun _ => 0)
    J M B hM hB.le (fun _ => by simpa using hs)
  let T := (correctedSmoothingThresholdFunctional J B hB.le).comp
    (Ring.inverse (correctedLowBandIdentityPlus J B))
  let F := fun E : ℝ => correctedScalarColumn J B hB.le (Real.sqrt (E / B) : ℂ)
  let G := fun E : ℝ => lowBandThresholdFunctional J B
    (correctedScalarColumnL1 J B hB.le (Real.sqrt (E / B) : ℂ))
  have hF : ν.Integrable F := correctedScalarColumn_signedIntegrable J B hB.le ν M hs'
  have hG : ν.Integrable G := (lowBandThresholdFunctional J B).integrable_comp
    (correctedScalarColumnL1_signedIntegrable J B hB.le ν M hs')
  have hT : ν.Integrable (fun E => T (F E)) := T.integrable_comp hF
  have hc : ν.Integrable (fun _ : ℝ => (-1 : ℂ)) := integrable_const _
  have hZ : ν.Integrable (fun E => scalarAnchorResponseHol J B hB.le
      (Real.sqrt (E / B) : ℂ)) := hc.sub (hG.sub hT)
  have hsuper : (∫ᵛ E, F E ∂<•ν) = f :=
    signedIntegral_correctedScalarColumn J B hB ν M hM hs'
  have hmass : (∫ᵛ E, G E ∂<•ν) =
      ∑ i, scalarThresholdCoefficient (J i) * ∫ e, f i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
    rw [signedIntegral_lowBandThresholdFunctional_correctedScalarColumnL1 J B hB ν M hs']
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply integral_congr_ae
    filter_upwards [correctedSignedResponseLp_coeFn (fun _ : Unit => ν) (fun _ => 0)
      (J i) M B hM hB.le (fun _ => by simpa using hs)] with e he
    change correctedSignedRowResponse ν 0 (J i) e =
      correctedSignedResponseLp (fun _ : Unit => ν) (fun _ => 0)
        (J i) M B hM hB.le (fun _ => by simpa using hs) e
    simpa only [correctedSignedResponse, Fintype.sum_unique] using he.symm
  have hzint : (∫ᵛ E, scalarAnchorResponseHol J B hB.le
      (Real.sqrt (E / B) : ℂ) ∂<•ν) =
      -(ν univ : ℂ) - ((∫ᵛ E, G E ∂<•ν) - T f) := by
    change (∫ᵛ E, (-1 : ℂ) - (G E - T (F E)) ∂<•ν) = _
    rw [VectorMeasure.integral_fun_sub (f := fun _ : ℝ => (-1 : ℂ))
      (g := fun E => G E - T (F E)) hc (hG.sub hT),
      VectorMeasure.integral_fun_sub (f := G) (g := fun E => T (F E)) hG hT,
      ← complexContinuousLinearMap_signedIntegral T hF, hsuper]
    simp
  unfold scalarAnchorResponsePhysical
  rw [← signedIntegral_re hZ, hzint, hmass]
  change -ν univ - ∑ i, (scalarThresholdCoefficient (J i)).re *
    correctedLowBandInverseSignedMeasure J B hB.le hunit f
      (correctedSignedResponseHilbert_integrable (fun _ : Unit => ν) (fun _ => 0)
        J M B hM hB.le (fun _ => by simpa using hs)) i univ = _
  rw [correctedLowBandInverseSignedMeasure_threshold_eq]
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
  rfl

end GapFamily.Analytic
