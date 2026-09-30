import GapFamily.Construction.FixedCutoffMarkerRepair
import GapFamily.Construction.MarkerReferenceInputBound
import GapFamily.Analytic.Kernel.FullKernelSignedResponseBound

/-!
# Uniform ordinary mass of marker transfer

The repaired signed input has one variation bound for every marker position
in the closed interval `[0,B]`, including the threshold endpoint. The same
bound is exponential in the cutoff and independent of the central charge.
-/

noncomputable section

open MeasureTheory Set Real
open scoped Classical BigOperators
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A bound for the ordinary variation norm of the canonical inverse. -/
def canonicalLocalInverseMassFactor (B : ℝ) : ℝ :=
  45 * correctedKernelBound * B ^ 3 +
    500 * correctedKernelBound ^ 2 * B ^ 6 *
      exp (correctedLowBandCoercivityExponent * B)

theorem canonicalLocalInverseMassFactor_nonneg (B : ℝ) (hB : 0 ≤ B) :
    0 ≤ canonicalLocalInverseMassFactor B := by
  have := correctedKernelBound_pos
  unfold canonicalLocalInverseMassFactor
  positivity

/-- Repair adds the inverse and its scalar threshold times the actual anchor. -/
def canonicalLocalRepairMassFactor (B : ℝ) : ℝ :=
  1 + canonicalLocalInverseMassFactor B *
    (1 + 3 * B * exp (canonicalLocalAnchorExponent * B))

theorem canonicalLocalRepairMassFactor_pos (B : ℝ) (hB : 0 ≤ B) :
    0 < canonicalLocalRepairMassFactor B := by
  have := canonicalLocalInverseMassFactor_nonneg B hB
  unfold canonicalLocalRepairMassFactor
  positivity

private theorem variation_real_add_le (μ ν : SignedMeasure ℝ) :
    (μ + ν).variation.real univ ≤ μ.variation.real univ + ν.variation.real univ := by
  simpa using signedMeasure_variation_real_sub_le μ (-ν)

private theorem variation_real_smul (μ : SignedMeasure ℝ) (c : ℝ) :
    (c • μ).variation.real univ = |c| * μ.variation.real univ := by
  simp [VectorMeasure.variation_smul, Measure.real, Measure.smul_apply,
    ENNReal.toReal_mul, Real.norm_eq_abs]

/-- Canonical repair is bounded on ordinary signed seed mass. -/
theorem signedSeedMass_canonicalLocalRepairInput_le (ν : ℤ → SignedMeasure ℝ)
    (B : ℝ) (hB : 1 ≤ B)
    (hν : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * B) :
    signedSeedMass (fun J : lowBandSpinSet B => canonicalLocalRepairInput ν B hB hν J) ≤
      canonicalLocalRepairMassFactor B * signedSeedMass (fun J : lowBandSpinSet B => ν J) := by
  have hB0 : 0 ≤ B := by linarith
  let S := lowBandSpinSet B
  let hunit := isUnit_correctedLowBandIdentityPlus_canonical B hB
  let μ := localInverseInput S ν (3 * B) B (by linarith) (by linarith) hν hunit
  let θ := canonicalLocalAnchorInput B hB
  let V := signedSeedMass (fun J : S => ν J)
  let U := ∑ j ∈ S, (μ j).variation.real univ
  let A := exp (canonicalLocalAnchorExponent * B)
  have hV : 0 ≤ V := signedSeedMass_nonneg _
  have hU : 0 ≤ U := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hI : 0 ≤ canonicalLocalInverseMassFactor B :=
    canonicalLocalInverseMassFactor_nonneg B (by linarith)
  have hμ : U ≤ canonicalLocalInverseMassFactor B * V := by
    dsimp [U, μ]
    rw [sum_totalVariation_localInverseInput_eq_native]
    apply (sum_totalVariation_correctedSignedInverseMeasure_le_physical
      (fun J : S => ν J) Subtype.val Subtype.val Subtype.val_injective B hB
      (fun J => (mem_lowBandSpinSet B J).mp J.property)
      (fun J => hν J J.property) hunit).trans
    apply mul_le_mul_of_nonneg_right _ hV
    unfold canonicalLocalInverseMassFactor
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (norm_correctedLowBandInverse_le_exp (fun J : S => (J : ℤ))
        Subtype.val_injective B hB (fun J => (mem_lowBandSpinSet B J).mp J.property))
      (by positivity))
  have ht : |finiteSignedThresholdMass S μ| ≤ 3 * B * U :=
    abs_finiteSignedThresholdMass_le_variation S μ B hB
      (fun J hJ => (mem_lowBandSpinSet B J).mp hJ)
  have hθ : (∑ j ∈ S, (θ j).variation.real univ) ≤ A :=
    sum_totalVariation_canonicalLocalAnchorInput_le_exp B hB
  have hraw : signedSeedMass
      (fun J : S => canonicalLocalRepairInput ν B hB hν J) ≤
      V + U + |finiteSignedThresholdMass S μ| *
        ∑ j ∈ S, (θ j).variation.real univ := by
    rw [signedSeedMass, Finset.sum_coe_sort S
      (fun j : ℤ => (canonicalLocalRepairInput ν B hB hν j).variation.real univ)]
    have hrow (j : ℤ) :
        (canonicalLocalRepairInput ν B hB hν j).variation.real univ ≤
          (ν j).variation.real univ + (μ j).variation.real univ +
            |finiteSignedThresholdMass S μ| * (θ j).variation.real univ := by
      change ((ν j - μ j) + finiteSignedThresholdMass S μ • θ j).variation.real univ ≤ _
      exact (variation_real_add_le _ _).trans
        (add_le_add (signedMeasure_variation_real_sub_le _ _)
          (variation_real_smul _ _).le)
    apply (Finset.sum_le_sum (fun j _ => hrow j)).trans
    have hVeq : (∑ j ∈ S, (ν j).variation.real univ) = V := by
      exact (Finset.sum_coe_sort S (fun j : ℤ => (ν j).variation.real univ)).symm
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hVeq]
    exact le_rfl
  calc
    _ ≤ V + U + (3 * B * U) * A := hraw.trans
      (add_le_add le_rfl (mul_le_mul ht hθ
        (Finset.sum_nonneg fun _ _ => measureReal_nonneg) (by positivity)))
    _ ≤ V + canonicalLocalInverseMassFactor B * V +
        (3 * B * (canonicalLocalInverseMassFactor B * V)) * A := by
      gcongr
    _ = _ := by dsimp [canonicalLocalRepairMassFactor, A]; ring

/-- Uniform in both the positive-marker and threshold-marker cases. -/
def fixedCutoffMarkerRepairMassBound (B : ℝ) : ℝ :=
  2 * canonicalLocalRepairMassFactor (2 * B)

theorem fixedCutoffMarkerRepairMassBound_pos (B : ℝ) (hB : 1 ≤ B) :
    0 < fixedCutoffMarkerRepairMassBound B := by
  exact mul_pos (by norm_num) (canonicalLocalRepairMassFactor_pos (2 * B) (by linarith))

/-- One ordinary mass budget works for all prescribed energies in `[0,B]`. -/
theorem signedSeedMass_fixedCutoffMarkerRepairInput_le (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) :
    signedSeedMass (fun J : lowBandSpinSet (2 * B) =>
      fixedCutoffMarkerRepairInput B δ hB hδ hδB J) ≤ fixedCutoffMarkerRepairMassBound B := by
  apply (signedSeedMass_canonicalLocalRepairInput_le
    (fixedCutoffMarkerTransfer B δ) (2 * B) (by linarith)
    (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB)).trans
  have hν : signedSeedMass (fun J : lowBandSpinSet (2 * B) =>
      fixedCutoffMarkerTransfer B δ J) ≤ 2 := by
    rw [signedSeedMass, Finset.sum_coe_sort (lowBandSpinSet (2 * B))
      (fun j : ℤ => (fixedCutoffMarkerTransfer B δ j).variation.real univ)]
    exact fixedCutoffMarkerTransfer_totalVariation_le _
      ((zero_mem_lowBandSpinSet (2 * B)).mpr (by linarith)) B δ
  simpa only [fixedCutoffMarkerRepairMassBound, mul_comm] using
    mul_le_mul_of_nonneg_left hν (canonicalLocalRepairMassFactor_pos (2 * B) (by linarith)).le

/-- A universal exponential rate for inverse variation. -/
def canonicalLocalInverseMassExponent : ℝ :=
  canonicalLocalAnchorPolynomial + correctedLowBandCoercivityExponent + 6

theorem canonicalLocalInverseMassExponent_pos : 0 < canonicalLocalInverseMassExponent := by
  have := canonicalLocalAnchorPolynomial_pos
  have := correctedLowBandCoercivityExponent_pos
  unfold canonicalLocalInverseMassExponent
  positivity

theorem canonicalLocalInverseMassFactor_le_exp (B : ℝ) (hB : 1 ≤ B) :
    canonicalLocalInverseMassFactor B ≤ exp (canonicalLocalInverseMassExponent * B) := by
  have hB0 : 0 ≤ B := by linarith
  have hK := correctedKernelBound_pos.le
  have hExp : 1 ≤ exp (correctedLowBandCoercivityExponent * B) :=
    one_le_exp (mul_nonneg correctedLowBandCoercivityExponent_pos.le hB0)
  have h3 : 45 * correctedKernelBound * B ^ 3 ≤
      45 * correctedKernelBound * B ^ 6 * exp (correctedLowBandCoercivityExponent * B) := by
    calc
      _ ≤ 45 * correctedKernelBound * B ^ 6 := by gcongr; norm_num
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hExp
  calc
    _ ≤ (45 * correctedKernelBound + 500 * correctedKernelBound ^ 2) *
        B ^ 6 * exp (correctedLowBandCoercivityExponent * B) := by
      unfold canonicalLocalInverseMassFactor
      nlinarith only [h3]
    _ ≤ canonicalLocalAnchorPolynomial * B ^ 6 *
        exp (correctedLowBandCoercivityExponent * B) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hB0 _)
      unfold canonicalLocalAnchorPolynomial
      linarith
    _ ≤ _ := polynomial_mul_exp_le_exp canonicalLocalAnchorPolynomial_pos.le hB 6

/-- One fixed rate controls the complete transfer repair for growing cutoffs. -/
def fixedCutoffMarkerRepairExponent : ℝ :=
  2 + 2 * (canonicalLocalInverseMassExponent + canonicalLocalAnchorExponent + 6)

theorem fixedCutoffMarkerRepairExponent_pos : 0 < fixedCutoffMarkerRepairExponent := by
  have := canonicalLocalInverseMassExponent_pos
  have := canonicalLocalAnchorExponent_pos
  unfold fixedCutoffMarkerRepairExponent
  positivity

private theorem canonicalLocalRepairMassFactor_le_exp (B : ℝ) (hB : 1 ≤ B) :
    canonicalLocalRepairMassFactor B ≤
      exp ((canonicalLocalInverseMassExponent + canonicalLocalAnchorExponent + 6) * B) := by
  let X := exp (canonicalLocalInverseMassExponent * B)
  let Y := exp (canonicalLocalAnchorExponent * B)
  have hB0 : 0 ≤ B := by linarith
  have hX : 1 ≤ X := one_le_exp
    (mul_nonneg canonicalLocalInverseMassExponent_pos.le hB0)
  have hY : 1 ≤ Y := one_le_exp
    (mul_nonneg canonicalLocalAnchorExponent_pos.le hB0)
  have hXY : 1 ≤ X * Y := one_le_mul_of_one_le_of_one_le hX hY
  have h1 : 1 ≤ B * (X * Y) := one_le_mul_of_one_le_of_one_le hB hXY
  have hXle : X ≤ B * (X * Y) := by
    calc
      X ≤ X * Y := le_mul_of_one_le_right (by linarith) hY
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hB
  calc
    _ ≤ 1 + X * (1 + 3 * B * Y) := by
      unfold canonicalLocalRepairMassFactor
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (canonicalLocalInverseMassFactor_le_exp B hB) (by positivity))
    _ ≤ 5 * B * (X * Y) := by nlinarith only [h1, hXle]
    _ = 5 * B ^ 1 *
        exp ((canonicalLocalInverseMassExponent + canonicalLocalAnchorExponent) * B) := by
      simp only [X, Y, pow_one, add_mul, exp_add]
    _ ≤ _ := by
      convert polynomial_mul_exp_le_exp (A := 5) (by norm_num) hB 1 using 1
      congr 1
      ring

theorem fixedCutoffMarkerRepairMassBound_le_exp (B : ℝ) (hB : 1 ≤ B) :
    fixedCutoffMarkerRepairMassBound B ≤ exp (fixedCutoffMarkerRepairExponent * B) := by
  calc
    _ ≤ 2 * exp ((canonicalLocalInverseMassExponent + canonicalLocalAnchorExponent + 6) *
        (2 * B)) := mul_le_mul_of_nonneg_left
      (canonicalLocalRepairMassFactor_le_exp (2 * B) (by linarith)) (by norm_num)
    _ = 2 * B ^ 0 * exp ((2 *
        (canonicalLocalInverseMassExponent + canonicalLocalAnchorExponent + 6)) * B) := by
      congr 2 <;> ring
    _ ≤ _ := by
      simpa only [fixedCutoffMarkerRepairExponent, Nat.cast_zero, add_zero] using
        polynomial_mul_exp_le_exp (A := 2) (by norm_num) hB 0

/-- The uniform transfer bound remains exponential as `B` grows. -/
theorem signedSeedMass_fixedCutoffMarkerRepairInput_le_exp (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) :
    signedSeedMass (fun J : lowBandSpinSet (2 * B) =>
      fixedCutoffMarkerRepairInput B δ hB hδ hδB J) ≤
        exp (fixedCutoffMarkerRepairExponent * B) :=
  (signedSeedMass_fixedCutoffMarkerRepairInput_le B δ hB hδ hδB).trans
    (fixedCutoffMarkerRepairMassBound_le_exp B hB)

/-- The exterior numerator correction has a bound independent of marker position. -/
theorem norm_correctedSignedResponse_fixedCutoffMarkerRepair_le (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) (e : ℝ) (j : ℤ)
    (he : |(j : ℝ)| ≤ e) (hBe : 2 * B ≤ e) :
    ‖correctedSignedResponse
      (fun J : lowBandSpinSet (2 * B) => fixedCutoffMarkerRepairInput B δ hB hδ hδB J)
      Subtype.val j e‖ ≤
      12 * correctedKernelBound * B * e * exp (fixedCutoffMarkerRepairExponent * B) := by
  have hB0 : 0 ≤ B := by linarith
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  calc
    _ ≤ signedSeedMass (fun J : lowBandSpinSet (2 * B) =>
        fixedCutoffMarkerRepairInput B δ hB hδ hδB J) *
          (6 * correctedKernelBound * (2 * B) * e) :=
      norm_correctedSignedResponse_le_exterior
        (fun J : lowBandSpinSet (2 * B) => fixedCutoffMarkerRepairInput B δ hB hδ hδB J)
        Subtype.val j (2 * B) (by linarith)
        (fun J => fixedCutoffMarkerRepairInput_physicalSupport B δ hB hδ hδB J J.property)
        e he hBe
    _ ≤ exp (fixedCutoffMarkerRepairExponent * B) *
          (6 * correctedKernelBound * (2 * B) * e) :=
      mul_le_mul_of_nonneg_right
        (signedSeedMass_fixedCutoffMarkerRepairInput_le_exp B δ hB hδ hδB)
        (by have := correctedKernelBound_pos; positivity)
    _ = _ := by ring

end GapFamily.Construction
