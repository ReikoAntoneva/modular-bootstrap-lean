import GapFamily.Analytic.Poincare.Repair.PoincareExteriorKernel
import GapFamily.Analytic.Kernel.FullKernelFiniteInputColumnSuperposition
import GapFamily.Analytic.Kernel.FullKernelInputColumnMass

/-! The exterior output of canonical local repair is the ordinary signed
superposition of its actual entire input kernel. The direct high-band anchor
density is retained, and the threshold atom is removed only by restriction.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set Real
open scoped BigOperators

variable (ν : ℤ → SignedMeasure ℝ) (B : ℝ) (hB : 1 ≤ B)
  (hν : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation,
    |(J : ℝ)| ≤ E ∧ E ≤ 3 * B)

/-- The inverse input used literally by canonical local repair. -/
def canonicalLocalInverseInput : ℤ → SignedMeasure ℝ :=
  localInverseInput (lowBandSpinSet B) ν (3 * B) B (by linarith)
    (zero_le_one.trans hB) hν (isUnit_correctedLowBandIdentityPlus_canonical B hB)

theorem canonicalLocalRepairInput_eq_sub_add :
    canonicalLocalRepairInput ν B hB hν = ν - canonicalLocalInverseInput ν B hB hν +
      finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalInverseInput ν B hB hν) •
        canonicalLocalAnchorInput B hB := rfl

theorem canonicalLocalInverseInput_physicalSupport (j : ℤ) :
    ∀ᵐ E ∂(canonicalLocalInverseInput ν B hB hν j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ 3 * B :=
  localInverseInput_ae_physical_le (lowBandSpinSet B) ν (3 * B) B (by linarith)
    (zero_le_one.trans hB) hν (isUnit_correctedLowBandIdentityPlus_canonical B hB)
    (3 * B) (by linarith) j

theorem canonicalLocalInverseInput_response (j : ℤ) (e : ℝ) :
    correctedSignedResponse (fun J : LowBandSpin B =>
      canonicalLocalInverseInput ν B hB hν J) Subtype.val j e =
    correctedKernelResponse (fun J : LowBandSpin B => (J : ℤ)) B
      (correctedLowBandInverse Subtype.val B
        (correctedSignedResponseHilbert (fun J : LowBandSpin B => ν J)
          Subtype.val Subtype.val (3 * B) B (by linarith) (zero_le_one.trans hB)
          (fun J => hν J J.property))) j e := by
  have hh : (fun J : LowBandSpin B => canonicalLocalInverseInput ν B hB hν J) =
      correctedSignedInverseMeasure (fun J : LowBandSpin B => ν J) Subtype.val
        Subtype.val (3 * B) B (by linarith) (zero_le_one.trans hB)
        (fun J => hν J J.property) (isUnit_correctedLowBandIdentityPlus_canonical B hB) := by
    funext J
    exact localInverseInput_apply _ _ _ _ _ _ _ _ J J.property
  rw [hh]
  exact correctedSignedResponse_correctedSignedInverseMeasure _ _ _ _ _ _ _ _ _ _ _

theorem canonicalLocalRepairInput_response (j : ℤ) (e : ℝ) :
    correctedSignedResponse (fun J : LowBandSpin B =>
      canonicalLocalRepairInput ν B hB hν J) Subtype.val j e =
      correctedSignedResponse (fun J : LowBandSpin B => ν J) Subtype.val j e -
        correctedSignedResponse (fun J : LowBandSpin B =>
          canonicalLocalInverseInput ν B hB hν J) Subtype.val j e +
        (finiteSignedThresholdMass (lowBandSpinSet B)
          (canonicalLocalInverseInput ν B hB hν) : ℂ) *
            correctedSignedResponse (fun J : LowBandSpin B =>
              canonicalLocalAnchorInput B hB J) Subtype.val j e := by
  let μ := canonicalLocalInverseInput ν B hB hν
  let θ := canonicalLocalAnchorInput B hB
  let a := finiteSignedThresholdMass (lowBandSpinSet B) μ
  have hμ : ∀ J : LowBandSpin B, ∀ᵐ E ∂(μ J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * B :=
    fun J => canonicalLocalInverseInput_physicalSupport ν B hB hν J
  have hθ : ∀ J : LowBandSpin B, ∀ᵐ E ∂(θ J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * B :=
    fun J => canonicalLocalAnchorInput_physicalSupport B hB J
  have hadd := correctedSignedResponse_add (fun J : LowBandSpin B => ν J - μ J)
    (fun J : LowBandSpin B => a • θ J) Subtype.val j (3 * B)
    (fun J => signedPhysicalSupport_sub (ν J) (μ J) J (3 * B) (hν J J.property) (hμ J))
    (fun J => signedPhysicalSupport_smul (θ J) J (3 * B) a (hθ J)) e
  have hsub := correctedSignedResponse_sub (fun J : LowBandSpin B => ν J)
    (fun J : LowBandSpin B => μ J) Subtype.val j (3 * B)
      (fun J => hν J J.property) hμ e
  have hscale := correctedSignedResponse_smul (fun J : LowBandSpin B => θ J)
    a Subtype.val j e
  have hid := congrArg (fun ρ : ℤ → SignedMeasure ℝ =>
    correctedSignedResponse (fun J : LowBandSpin B => ρ J) Subtype.val j e)
      (canonicalLocalRepairInput_eq_sub_add ν B hB hν)
  exact hid.trans (hadd.trans (congrArg₂ (· + ·) hsub hscale))

/-- The actual exterior numerator is expressed through ordinary compact
signed input integration, with the actual square-root input coordinate. -/
def canonicalRepairExteriorNumerator (j : ℤ) (e : ℝ) : ℂ :=
  ∑ J : LowBandSpin B, ∫ᵛ E,
    canonicalRepairKernelHol B hB j J e (sqrt (E - |(J : ℝ)|) : ℂ) ∂<•(ν J)

include hν in
theorem canonicalRepairKernelHol_signedIntegrable (jin j : ℤ) (e : ℝ)
    (he : |(j : ℝ)| ≤ e) (hjin : jin ∈ lowBandSpinSet B) :
    (ν jin).Integrable (fun E =>
      canonicalRepairKernelHol B hB j jin e (sqrt (E - |(jin : ℝ)|) : ℂ)) := by
  have hp := correctedSignedRowResponse_integrable (ν jin) jin j (3 * B) (hν jin hjin) e
  have hi := correctedKernelResponse_inputInverseColumn_signedIntegrable
    (fun J : LowBandSpin B => (J : ℤ)) B (zero_le_one.trans hB) jin
      (ν jin) (3 * B) (hν jin hjin) j e he
  have ht := correctedInputInverseThreshold_signedIntegrable
    (fun J : LowBandSpin B => (J : ℤ)) B (zero_le_one.trans hB) jin
      (ν jin) (3 * B) (hν jin hjin)
  apply ((hp.sub hi).add (ht.mul_const
    (canonicalAnchorExteriorNumerator B hB j e : ℂ))).congr
  filter_upwards [hν jin hjin] with E hE
  exact (canonicalRepairKernelHol_sqrt B hB j jin e E hE.1).symm

/-- The threshold of the literal canonical inverse is the finite ordinary
signed pairing with its inverse threshold columns. -/
theorem canonicalLocalInverseInput_threshold :
    finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalInverseInput ν B hB hν) =
      ∑ J : LowBandSpin B, ∫ᵛ E,
        (correctedInputInverseThreshold (fun J : LowBandSpin B => (J : ℤ)) B
          (zero_le_one.trans hB) J (sqrt (E - |(J : ℝ)|) : ℂ)).re ∂<•(ν J) := by
  calc
    _ = ∑ J : LowBandSpin B, (PoincareScalarFourier.scalarThresholdCoefficient J).re *
        correctedSignedInverseMeasure (fun J : LowBandSpin B => ν J) Subtype.val
          Subtype.val (3 * B) B (by linarith) (zero_le_one.trans hB)
          (fun J => hν J J.property) (isUnit_correctedLowBandIdentityPlus_canonical B hB)
          J univ := by
      unfold finiteSignedThresholdMass
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro J _
      congr 1
      exact congrArg (fun μ : SignedMeasure ℝ => μ univ)
        (localInverseInput_apply _ _ _ _ _ _ _ _ J J.property)
    _ = _ := (sum_signedIntegral_correctedInputInverseThreshold
      (fun J : LowBandSpin B => ν J) Subtype.val Subtype.val (3 * B) B
      (by linarith) (zero_le_one.trans hB) (fun J => hν J J.property)
      (isUnit_correctedLowBandIdentityPlus_canonical B hB)).symm

theorem canonicalLocalInverseInput_threshold_complex :
    (finiteSignedThresholdMass (lowBandSpinSet B)
      (canonicalLocalInverseInput ν B hB hν) : ℂ) =
      ∑ J : LowBandSpin B, ∫ᵛ E,
        correctedInputInverseThreshold (fun J : LowBandSpin B => (J : ℤ)) B
          (zero_le_one.trans hB) J (sqrt (E - |(J : ℝ)|) : ℂ) ∂<•(ν J) := by
  rw [canonicalLocalInverseInput_threshold, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro J _
  have ht := correctedInputInverseThreshold_signedIntegrable
    (fun J : LowBandSpin B => (J : ℤ)) B (zero_le_one.trans hB) J
      (ν J) (3 * B) (hν J J.property)
  have htr : (ν J).Integrable (fun E =>
      (correctedInputInverseThreshold (fun J : LowBandSpin B => (J : ℤ)) B
        (zero_le_one.trans hB) J (sqrt (E - |(J : ℝ)|) : ℂ)).re) := ht.re
  rw [← signedIntegral_complex_ofReal htr]
  apply VectorMeasure.integral_congr_ae
  filter_upwards with E
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im,
      correctedInputInverseThreshold_ofReal_im _ _ _
        (isUnit_correctedLowBandIdentityPlus_canonical B hB)]

include hν in
theorem signedIntegral_canonicalRepairKernelHol (jin j : ℤ) (e : ℝ)
    (he : |(j : ℝ)| ≤ e) (hjin : jin ∈ lowBandSpinSet B) :
    (∫ᵛ E, canonicalRepairKernelHol B hB j jin e
      (sqrt (E - |(jin : ℝ)|) : ℂ) ∂<•(ν jin)) =
      correctedSignedRowResponse (ν jin) jin j e -
        (∫ᵛ E, correctedKernelResponse (fun J : LowBandSpin B => (J : ℤ)) B
          (correctedInputInverseColumn Subtype.val B (zero_le_one.trans hB) jin
            (sqrt (E - |(jin : ℝ)|) : ℂ)) j e ∂<•(ν jin)) +
        (∫ᵛ E, correctedInputInverseThreshold (fun J : LowBandSpin B => (J : ℤ)) B
          (zero_le_one.trans hB) jin (sqrt (E - |(jin : ℝ)|) : ℂ) ∂<•(ν jin)) *
            (canonicalAnchorExteriorNumerator B hB j e : ℂ) := by
  have hp := correctedSignedRowResponse_integrable (ν jin) jin j (3 * B) (hν jin hjin) e
  have hi := correctedKernelResponse_inputInverseColumn_signedIntegrable
    (fun J : LowBandSpin B => (J : ℤ)) B (zero_le_one.trans hB) jin
      (ν jin) (3 * B) (hν jin hjin) j e he
  have ht := correctedInputInverseThreshold_signedIntegrable
    (fun J : LowBandSpin B => (J : ℤ)) B (zero_le_one.trans hB) jin
      (ν jin) (3 * B) (hν jin hjin)
  calc
    _ = ∫ᵛ E, correctedKernel j jin e E -
        correctedKernelResponse (fun J : LowBandSpin B => (J : ℤ)) B
          (correctedInputInverseColumn Subtype.val B (zero_le_one.trans hB) jin
            (sqrt (E - |(jin : ℝ)|) : ℂ)) j e +
        correctedInputInverseThreshold (fun J : LowBandSpin B => (J : ℤ)) B
          (zero_le_one.trans hB) jin (sqrt (E - |(jin : ℝ)|) : ℂ) *
            (canonicalAnchorExteriorNumerator B hB j e : ℂ) ∂<•(ν jin) := by
      apply VectorMeasure.integral_congr_ae
      filter_upwards [hν jin hjin] with E hE
      exact canonicalRepairKernelHol_sqrt B hB j jin e E hE.1
    _ = _ := by
      rw [VectorMeasure.integral_fun_add
        (f := fun E => correctedKernel j jin e E -
          correctedKernelResponse (fun J : LowBandSpin B => (J : ℤ)) B
            (correctedInputInverseColumn Subtype.val B (zero_le_one.trans hB) jin
              (sqrt (E - |(jin : ℝ)|) : ℂ)) j e)
        (g := fun E => correctedInputInverseThreshold (fun J : LowBandSpin B => (J : ℤ)) B
          (zero_le_one.trans hB) jin (sqrt (E - |(jin : ℝ)|) : ℂ) *
            (canonicalAnchorExteriorNumerator B hB j e : ℂ))
        (hp.sub hi) (ht.mul_const _),
        VectorMeasure.integral_fun_sub
          (f := fun E => correctedKernel j jin e E)
          (g := fun E => correctedKernelResponse (fun J : LowBandSpin B => (J : ℤ)) B
            (correctedInputInverseColumn Subtype.val B (zero_le_one.trans hB) jin
              (sqrt (E - |(jin : ℝ)|) : ℂ)) j e) hp hi]
      congr 1
      simp_rw [mul_comm _ (canonicalAnchorExteriorNumerator B hB j e : ℂ)]
      exact signedIntegral_const_mul ht _

/-- The signed integral kernel is exactly the exterior response of the
actual original input, its actual inverse, and the full normalized anchor. -/
theorem canonicalRepairExteriorNumerator_eq (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    canonicalRepairExteriorNumerator ν B hB j e =
      correctedSignedResponse (fun J : LowBandSpin B => ν J) Subtype.val j e -
        correctedSignedResponse (fun J : LowBandSpin B =>
          canonicalLocalInverseInput ν B hB hν J) Subtype.val j e +
        (finiteSignedThresholdMass (lowBandSpinSet B)
          (canonicalLocalInverseInput ν B hB hν) : ℂ) *
            (canonicalAnchorExteriorNumerator B hB j e : ℂ) := by
  unfold canonicalRepairExteriorNumerator
  simp_rw [signedIntegral_canonicalRepairKernelHol ν B hB hν _ j e he (Subtype.mem _)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_signedIntegral_correctedKernelResponse_inputInverseColumn
      (fun J : LowBandSpin B => ν J) Subtype.val Subtype.val (3 * B) B
        (by linarith) (zero_le_one.trans hB) (fun J => hν J J.property) j e he,
    ← canonicalLocalInverseInput_response ν B hB hν j e,
    ← canonicalLocalInverseInput_threshold_complex ν B hB hν]
  rfl

include hν in
/-- The integrated exterior numerator is real at every physical output energy. -/
theorem canonicalRepairExteriorNumerator_im (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    (canonicalRepairExteriorNumerator ν B hB j e).im = 0 := by
  rw [canonicalRepairExteriorNumerator_eq ν B hB hν j e he,
    Complex.add_im, Complex.sub_im,
    correctedSignedResponse_im (fun J : LowBandSpin B => ν J) Subtype.val j (3 * B)
      (fun J => hν J J.property) e,
    correctedSignedResponse_im
      (fun J : LowBandSpin B => canonicalLocalInverseInput ν B hB hν J)
      Subtype.val j (3 * B)
      (fun J => canonicalLocalInverseInput_physicalSupport ν B hB hν J) e]
  simp only [Complex.mul_im, Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero]

end GapFamily.Analytic
