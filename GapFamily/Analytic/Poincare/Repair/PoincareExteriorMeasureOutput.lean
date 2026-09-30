import GapFamily.Analytic.Poincare.Repair.PoincareExteriorReconstruction
import GapFamily.Analytic.Poincare.Repair.PoincareAnchorExteriorOutput

/-! The ordinary thermal output measure of canonical local repair on the
exterior is the signed superposition of its actual entire kernel. The direct
high scalar-band anchor density is included, with ordinary integrability.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set
open scoped Classical BigOperators

private theorem signedMeasure_restrict_Ioi_eq_zero_of_ae_le
    (ν : SignedMeasure ℝ) (B : ℝ) (hν : ∀ᵐ E ∂ν.variation, E ≤ B) :
    ν.restrict (Ioi B) = 0 := by
  apply VectorMeasure.variation_eq_zero.mp
  rw [VectorMeasure.variation_restrict measurableSet_Ioi, Measure.restrict_eq_zero,
    measure_eq_zero_iff_ae_notMem]
  exact hν.mono fun _ hE => not_lt_of_ge hE

variable (ν : ℤ → SignedMeasure ℝ) (B : ℝ) (hB : 1 ≤ B)
  (hν : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation,
    |(J : ℝ)| ≤ E ∧ E ≤ 3 * B)

/-- The direct repaired input above the cutoff consists precisely of the
actual high-band anchor input multiplied by the inverse threshold mass. -/
theorem canonicalLocalRepairInput_restrict_Ioi
    (hinside : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation, E < B)
    (j : ℤ) (hj : j ∈ lowBandSpinSet B) :
    (canonicalLocalRepairInput ν B hB hν j).restrict (Ioi B) =
      finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalInverseInput ν B hB hν) •
        (canonicalLocalAnchorInput B hB j).restrict (Ioi B) := by
  have hin : (ν j).restrict (Ioi B) = 0 :=
    signedMeasure_restrict_Ioi_eq_zero_of_ae_le (ν j) B
      ((hinside j hj).mono fun _ hE => hE.le)
  have hi : (canonicalLocalInverseInput ν B hB hν j).restrict (Ioi B) = 0 :=
    localInverseInput_restrict_Ioi _ _ _ _ _ _ _ _ _
  rw [canonicalLocalRepairInput_eq_sub_add]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    VectorMeasure.restrict_add, VectorMeasure.restrict_sub, VectorMeasure.restrict_smul,
    hin, hi, sub_self, zero_add]

/-- The exterior direct input retains exactly the ordinary anchor density. -/
theorem canonicalLocalRepair_directExterior_thermal
    (hinside : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation, E < B)
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (if j ∈ lowBandSpinSet B then
      thermalSignedInputMeasure ((canonicalLocalRepairInput ν B hB hν j).restrict (Ioi B)) t
      else 0) =
      ((referenceMeasure j).restrict (Ioi B)).withDensityᵥ
        (fun e => finiteSignedThresholdMass (lowBandSpinSet B)
          (canonicalLocalInverseInput ν B hB hν) * (Real.exp (-t * e) *
          (if j = 0 then scalarAnchorNumerator B
            (scalarAnchorResponsePhysical (fun J : lowBandSpinSet B => (J : ℤ)) B
              (zero_le_one.trans hB)) e else 0))) := by
  let a := finiteSignedThresholdMass (lowBandSpinSet B)
    (canonicalLocalInverseInput ν B hB hν)
  have hd : (if j ∈ lowBandSpinSet B then
      thermalSignedInputMeasure ((canonicalLocalRepairInput ν B hB hν j).restrict (Ioi B)) t
      else 0) = a • (if j ∈ lowBandSpinSet B then
      thermalSignedInputMeasure ((canonicalLocalAnchorInput B hB j).restrict (Ioi B)) t
      else 0) := by
    by_cases hj : j ∈ lowBandSpinSet B
    · rw [ite_eq_left hj, ite_eq_left hj,
        canonicalLocalRepairInput_restrict_Ioi ν B hB hν hinside j hj]
      apply thermalSignedInputMeasure_smul _ a j (3 * B) _ ht
      rw [VectorMeasure.variation_restrict measurableSet_Ioi]
      exact ae_restrict_of_ae (canonicalLocalAnchorInput_physicalSupport B hB j)
    · simp only [ite_eq_right hj, smul_zero]
  rw [hd, canonicalLocalAnchor_directExterior_thermal B hB j ht.le,
    ← withDensityᵥ_smul']
  rfl

/-- On the physical output range, the signed kernel numerator is exactly the
actual repair response plus its literal exterior direct anchor numerator. -/
theorem canonicalRepairExteriorNumerator_re_eq
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    (canonicalRepairExteriorNumerator ν B hB j e).re =
      finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalInverseInput ν B hB hν) *
        (if j = 0 then scalarAnchorNumerator B
          (scalarAnchorResponsePhysical (fun J : lowBandSpinSet B => (J : ℤ)) B
            (zero_le_one.trans hB)) e else 0) +
      (correctedSignedResponse (fun J : LowBandSpin B =>
        canonicalLocalRepairInput ν B hB hν J) Subtype.val j e).re := by
  have hr := congrArg Complex.re (canonicalLocalRepairInput_response ν B hB hν j e)
  have hn := congrArg Complex.re (canonicalRepairExteriorNumerator_eq ν B hB hν j e he)
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hr hn
  rw [canonicalAnchorExteriorNumerator] at hn
  rw [hn, hr]
  ring

include hν in
/-- The full kernel numerator has an ordinary absolutely convergent thermal
integral against the physical reference measure. -/
theorem integrable_canonicalRepairExteriorNumerator_thermal
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun e => Real.exp (-t * e) *
      (canonicalRepairExteriorNumerator ν B hB j e).re) (referenceMeasure j) := by
  have hd := (integrable_canonicalAnchorDirectNumerator_thermal B hB j ht.le).const_mul
    (finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalInverseInput ν B hB hν))
  have hr := integrable_finiteCorrectedThermalDensity (lowBandSpinSet B)
    (canonicalLocalRepairInput ν B hB hν) j (3 * B)
    (canonicalLocalRepairInput_physicalSupport ν B hB hν) ht
  apply (hd.add hr).congr
  filter_upwards [referenceMeasure_ae_above_edge j] with e he
  rw [canonicalRepairExteriorNumerator_re_eq ν B hB hν j e he.le]
  simp only [Pi.add_apply]
  ring

/-- The actual canonical repair output strictly above the cutoff is the
ordinary density obtained by integrating the actual entire repair kernel. -/
theorem canonicalLocalRepairOutput_restrict_exterior
    (hinside : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation, E < B)
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalRepairInput ν B hB hν) j t).restrict (Ioi B) =
      ((referenceMeasure j).restrict (Ioi B)).withDensityᵥ
        (fun e => Real.exp (-t * e) *
          (canonicalRepairExteriorNumerator ν B hB j e).re) := by
  rw [correctedThermalFiniteOutputMeasure_restrict_Ioi (lowBandSpinSet B)
    (canonicalLocalRepairInput ν B hB hν) j (3 * B)
    (canonicalLocalRepairInput_physicalSupport ν B hB hν) ht B (zero_le_one.trans hB),
    canonicalLocalRepair_directExterior_thermal ν B hB hν hinside j ht]
  rw [← withDensityᵥ_add'
    ((integrable_canonicalAnchorDirectNumerator_thermal B hB j ht.le).const_mul
      (finiteSignedThresholdMass (lowBandSpinSet B)
        (canonicalLocalInverseInput ν B hB hν))).restrict
    (integrable_finiteCorrectedThermalDensity (lowBandSpinSet B)
      (canonicalLocalRepairInput ν B hB hν) j (3 * B)
      (canonicalLocalRepairInput_physicalSupport ν B hB hν) ht).restrict]
  apply WithDensityᵥEq.congr_ae
  filter_upwards [ae_restrict_of_ae (referenceMeasure_ae_above_edge j)] with e he
  rw [canonicalRepairExteriorNumerator_re_eq ν B hB hν j e he.le]
  ring

/-- The exterior output in the partition-function height convention has the
literal weight `exp (-2π t e)`. -/
theorem canonicalLocalRepairOutput_restrict_exterior_height
    (hinside : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation, E < B)
    (j : ℤ) (t : ℝ) (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalRepairInput ν B hB hν) j (2 * Real.pi * t)).restrict (Ioi B) =
      ((referenceMeasure j).restrict (Ioi B)).withDensityᵥ
        (fun e => Real.exp (-2 * Real.pi * t * e) *
          (canonicalRepairExteriorNumerator ν B hB j e).re) := by
  simpa only [neg_mul] using canonicalLocalRepairOutput_restrict_exterior
    ν B hB hν hinside j (show 0 < 2 * Real.pi * t by positivity)

end GapFamily.Analytic
