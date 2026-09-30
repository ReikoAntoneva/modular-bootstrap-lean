import GapFamily.Construction.FixedCutoffMarkerTransferBound
import GapFamily.Analytic.Poincare.Repair.PoincareExteriorReconstruction
import GapFamily.Analytic.Poincare.Repair.PoincareAnchorExteriorBound

/-!
# Complete exterior bound for marker transfer

The exterior numerator includes the scalar anchor's direct density on
`[4B,6B]`. Its bound is uniform in the prescribed marker position and has
only linear growth in the output energy.
-/

noncomputable section

open MeasureTheory Set Real
open scoped Classical BigOperators
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The actual local inverse is bounded on ordinary signed seed mass. -/
theorem signedSeedMass_canonicalLocalInverseInput_le_exp (ν : ℤ → SignedMeasure ℝ)
    (B : ℝ) (hB : 1 ≤ B)
    (hν : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * B) :
    signedSeedMass (fun J : lowBandSpinSet B => canonicalLocalInverseInput ν B hB hν J) ≤
      exp (canonicalLocalInverseMassExponent * B) *
        signedSeedMass (fun J : lowBandSpinSet B => ν J) := by
  let S := lowBandSpinSet B
  let hunit := isUnit_correctedLowBandIdentityPlus_canonical B hB
  have hraw : signedSeedMass
      (fun J : S => canonicalLocalInverseInput ν B hB hν J) ≤
        canonicalLocalInverseMassFactor B * signedSeedMass (fun J : S => ν J) := by
    rw [signedSeedMass, Finset.sum_coe_sort S
      (fun j : ℤ => (canonicalLocalInverseInput ν B hB hν j).variation.real univ)]
    unfold canonicalLocalInverseInput
    rw [sum_totalVariation_localInverseInput_eq_native]
    apply (sum_totalVariation_correctedSignedInverseMeasure_le_physical
      (fun J : S => ν J) Subtype.val Subtype.val Subtype.val_injective B hB
      (fun J => (mem_lowBandSpinSet B J).mp J.property)
      (fun J => hν J J.property) hunit).trans
    apply mul_le_mul_of_nonneg_right _ (signedSeedMass_nonneg _)
    unfold canonicalLocalInverseMassFactor
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (norm_correctedLowBandInverse_le_exp (fun J : S => (J : ℤ))
        Subtype.val_injective B hB (fun J => (mem_lowBandSpinSet B J).mp J.property))
      (by positivity))
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (canonicalLocalInverseMassFactor_le_exp B hB) (signedSeedMass_nonneg _))

/-- A universal rate controlling the direct anchor and all inverse responses. -/
def fixedCutoffMarkerTransferExteriorExponent : ℝ :=
  (48 * correctedKernelBound + 12) +
    2 * (canonicalLocalInverseMassExponent + canonicalAnchorExteriorExponent) + 1

theorem fixedCutoffMarkerTransferExteriorExponent_pos :
    0 < fixedCutoffMarkerTransferExteriorExponent := by
  have := correctedKernelBound_pos
  have := canonicalLocalInverseMassExponent_pos
  have := canonicalAnchorExteriorExponent_pos
  unfold fixedCutoffMarkerTransferExteriorExponent
  positivity

/-- Complete exterior numerator, including its direct high scalar band. -/
theorem norm_canonicalRepairExteriorNumerator_fixedCutoffMarkerTransfer_le
    (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B)
    (e : ℝ) (j : ℤ) (he : |(j : ℝ)| ≤ e) (hBe : 2 * B ≤ e) :
    ‖canonicalRepairExteriorNumerator (fixedCutoffMarkerTransfer B δ)
      (2 * B) (by linarith) j e‖ ≤
        e * exp (fixedCutoffMarkerTransferExteriorExponent * B) := by
  have hB0 : 0 ≤ B := by linarith
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hK := correctedKernelBound_pos.le
  let hcut : 1 ≤ 2 * B := by linarith
  let ν := fixedCutoffMarkerTransfer B δ
  let hs := fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB
  let μ := canonicalLocalInverseInput ν (2 * B) hcut hs
  let X := exp (canonicalLocalInverseMassExponent * (2 * B))
  let A := exp (canonicalAnchorExteriorExponent * (2 * B))
  have hX : 1 ≤ X := one_le_exp
    (mul_nonneg canonicalLocalInverseMassExponent_pos.le (by positivity))
  have hA : 1 ≤ A := one_le_exp
    (mul_nonneg canonicalAnchorExteriorExponent_pos.le (by positivity))
  have hνmass : signedSeedMass (fun J : lowBandSpinSet (2 * B) => ν J) ≤ 2 := by
    rw [signedSeedMass, Finset.sum_coe_sort (lowBandSpinSet (2 * B))
      (fun j : ℤ => (ν j).variation.real univ)]
    exact fixedCutoffMarkerTransfer_totalVariation_le _
      ((zero_mem_lowBandSpinSet (2 * B)).mpr (by linarith)) B δ
  have hμmass : signedSeedMass (fun J : lowBandSpinSet (2 * B) => μ J) ≤ 2 * X := by
    apply (signedSeedMass_canonicalLocalInverseInput_le_exp ν (2 * B) hcut hs).trans
    simpa only [X, mul_comm] using
      mul_le_mul_of_nonneg_left hνmass (exp_pos (canonicalLocalInverseMassExponent * (2 * B))).le
  have hνresponse : ‖correctedSignedResponse
      (fun J : lowBandSpinSet (2 * B) => ν J) Subtype.val j e‖ ≤
        24 * correctedKernelBound * B * e := by
    apply (norm_correctedSignedResponse_le_exterior
      (fun J : lowBandSpinSet (2 * B) => ν J) Subtype.val j (2 * B) hcut
      (fun J => hs J J.property) e he hBe).trans
    calc
      _ ≤ 2 * (6 * correctedKernelBound * (2 * B) * e) :=
        mul_le_mul_of_nonneg_right hνmass (by positivity)
      _ = _ := by ring
  have hμresponse : ‖correctedSignedResponse
      (fun J : lowBandSpinSet (2 * B) => μ J) Subtype.val j e‖ ≤
        24 * correctedKernelBound * B * e * X := by
    apply (norm_correctedSignedResponse_le_exterior
      (fun J : lowBandSpinSet (2 * B) => μ J) Subtype.val j (2 * B) hcut
      (fun J => canonicalLocalInverseInput_physicalSupport ν (2 * B) hcut hs J)
      e he hBe).trans
    calc
      _ ≤ (2 * X) * (6 * correctedKernelBound * (2 * B) * e) :=
        mul_le_mul_of_nonneg_right hμmass (by positivity)
      _ = _ := by ring
  have hthreshold : |finiteSignedThresholdMass (lowBandSpinSet (2 * B)) μ| ≤
      12 * B * X := by
    apply (abs_finiteSignedThresholdMass_le_variation (lowBandSpinSet (2 * B))
      μ (2 * B) hcut (fun J hJ => (mem_lowBandSpinSet (2 * B) J).mp hJ)).trans
    have hμsum : (∑ J ∈ lowBandSpinSet (2 * B), (μ J).variation.real univ) ≤ 2 * X := by
      simpa only [signedSeedMass, Finset.sum_coe_sort (lowBandSpinSet (2 * B))
        (fun J : ℤ => (μ J).variation.real univ)] using hμmass
    calc
      _ ≤ 3 * (2 * B) * (2 * X) := mul_le_mul_of_nonneg_left hμsum (by positivity)
      _ = _ := by ring
  have hanchor : |canonicalAnchorExteriorNumerator (2 * B) hcut j e| ≤ e * A :=
    abs_canonicalAnchorExteriorNumerator_le_energy_mul_exp (2 * B) hcut j e he hBe
  have hraw : ‖canonicalRepairExteriorNumerator ν (2 * B) hcut j e‖ ≤
      (24 * correctedKernelBound * B * e + 24 * correctedKernelBound * B * e * X) +
        (12 * B * X) * (e * A) := by
    rw [canonicalRepairExteriorNumerator_eq ν (2 * B) hcut hs j e he]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (norm_sub_le _ _).trans (add_le_add hνresponse hμresponse)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hthreshold hanchor (abs_nonneg _) (by positivity)
  have hXA : 1 ≤ X * A := one_le_mul_of_one_le_of_one_le hX hA
  have hXXA : X ≤ X * A := le_mul_of_one_le_right (by linarith) hA
  have hC0 : 0 ≤ 24 * correctedKernelBound * B * e := by positivity
  calc
    _ ≤ (24 * correctedKernelBound * B * e + 24 * correctedKernelBound * B * e * X) +
        (12 * B * X) * (e * A) := hraw
    _ ≤ (48 * correctedKernelBound + 12) * B * e * (X * A) := by
      nlinarith only [mul_le_mul_of_nonneg_left hXA hC0,
        mul_le_mul_of_nonneg_left hXXA hC0]
    _ = e * ((48 * correctedKernelBound + 12) * B ^ 1 *
        exp ((2 * (canonicalLocalInverseMassExponent + canonicalAnchorExteriorExponent)) * B)) := by
      have hexp : X * A =
          exp ((2 * (canonicalLocalInverseMassExponent + canonicalAnchorExteriorExponent)) * B) := by
        dsimp [X, A]
        rw [← exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ he0
      simpa only [fixedCutoffMarkerTransferExteriorExponent, Nat.cast_one] using
        polynomial_mul_exp_le_exp (A := 48 * correctedKernelBound + 12)
          (D := 2 * (canonicalLocalInverseMassExponent + canonicalAnchorExteriorExponent))
          (by positivity) hB 1

/-- The ordinary real numerator obeys the same complete exterior estimate. -/
theorem abs_re_canonicalRepairExteriorNumerator_fixedCutoffMarkerTransfer_le
    (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B)
    (e : ℝ) (j : ℤ) (he : |(j : ℝ)| ≤ e) (hBe : 2 * B ≤ e) :
    |(canonicalRepairExteriorNumerator (fixedCutoffMarkerTransfer B δ)
      (2 * B) (by linarith) j e).re| ≤
        e * exp (fixedCutoffMarkerTransferExteriorExponent * B) :=
  (Complex.abs_re_le_norm _).trans
    (norm_canonicalRepairExteriorNumerator_fixedCutoffMarkerTransfer_le B δ hB hδ hδB e j he hBe)

end GapFamily.Construction
