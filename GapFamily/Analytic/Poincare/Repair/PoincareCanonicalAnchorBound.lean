import GapFamily.Analytic.Poincare.Repair.PoincareCanonicalLocalRepair
import GapFamily.Analytic.Poincare.Repair.PoincareLocalAnchorVariation
import GapFamily.Analytic.Kernel.FullKernelScalarAnchorMeasureBound

/-!
# Ordinary mass of the canonical anchor

The literal high-band anchor input minus its actual low-band inverse response
has uniformly exponential total variation. The estimate uses the genuine
normalized scalar measure and the proved norm of the actual inverse.
-/

noncomputable section

open MeasureTheory Set Real
open scoped BigOperators

namespace GapFamily.Analytic

/-- The coefficient of the physical inverse's degree-six variation bound. -/
def canonicalLocalAnchorPolynomial : ℝ :=
  1 + 45 * correctedKernelBound + 500 * correctedKernelBound ^ 2

theorem canonicalLocalAnchorPolynomial_pos : 0 < canonicalLocalAnchorPolynomial := by
  have := correctedKernelBound_pos
  unfold canonicalLocalAnchorPolynomial
  positivity

/-- One universal rate includes the scalar seed mass and the actual inverse. -/
def canonicalLocalAnchorExponent : ℝ :=
  canonicalLocalAnchorPolynomial + correctedLowBandCoercivityExponent +
    scalarAnchorMeasureExponent + 6

theorem canonicalLocalAnchorExponent_pos : 0 < canonicalLocalAnchorExponent := by
  have := canonicalLocalAnchorPolynomial_pos
  have := correctedLowBandCoercivityExponent_pos
  have := scalarAnchorMeasureExponent_pos
  unfold canonicalLocalAnchorExponent
  positivity

private theorem anchor_inverse_variation_coefficient_le (B N : ℝ) (hB : 1 ≤ B)
    (hN : N ≤ exp (correctedLowBandCoercivityExponent * B)) :
    1 + 45 * correctedKernelBound * B ^ 3 + 500 * correctedKernelBound ^ 2 * B ^ 6 * N ≤
      canonicalLocalAnchorPolynomial * B ^ 6 * exp (correctedLowBandCoercivityExponent * B) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC := correctedKernelBound_pos.le
  have hD := correctedLowBandCoercivityExponent_pos.le
  have hExp : 1 ≤ exp (correctedLowBandCoercivityExponent * B) :=
    one_le_exp_iff.mpr (mul_nonneg hD hB0)
  have h1 : 1 ≤ B ^ 6 * exp (correctedLowBandCoercivityExponent * B) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB) hExp
  have h3 : 45 * correctedKernelBound * B ^ 3 ≤
      45 * correctedKernelBound * B ^ 6 * exp (correctedLowBandCoercivityExponent * B) := by
    calc
      _ ≤ 45 * correctedKernelBound * B ^ 6 := by
        gcongr
        norm_num
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hExp
  calc
    _ ≤ B ^ 6 * exp (correctedLowBandCoercivityExponent * B) +
        45 * correctedKernelBound * B ^ 6 * exp (correctedLowBandCoercivityExponent * B) +
        500 * correctedKernelBound ^ 2 * B ^ 6 * exp (correctedLowBandCoercivityExponent * B) :=
      add_le_add (add_le_add h1 h3) (mul_le_mul_of_nonneg_left hN (by positivity))
    _ = _ := by unfold canonicalLocalAnchorPolynomial; ring

/-- The actual normalized anchor has exponential ordinary mass on every finite
physical spin set containing the scalar row. -/
theorem sum_totalVariation_actualLocalAnchorInput_le_exp
    (S : Finset ℤ) (h0 : 0 ∈ S) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ j ∈ S, |(j : ℝ)| < B)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) :
    (∑ j ∈ S, (actualLocalAnchorInput S B (by linarith) hunit j).variation.real univ) ≤
      exp (canonicalLocalAnchorExponent * B) := by
  let J : S → ℤ := fun j => (j : ℤ)
  have hJ : Function.Injective J := Subtype.val_injective
  have hphysical : ∀ j : S, |(J j : ℝ)| < B := fun j => hband j j.property
  have hInv := norm_correctedLowBandInverse_le_exp J hJ B hB hphysical
  have hMass := scalarAnchorBandMeasure_actual_totalVariation_le_exp J hJ B hB hphysical
  have hP := canonicalLocalAnchorPolynomial_pos
  have hRaw := sum_totalVariation_localAnchorInput_le S h0 B hB hband
    (scalarAnchorResponsePhysical J B (by linarith))
    (continuous_scalarAnchorResponsePhysical J B (by linarith)).continuousOn hunit
  change (∑ j ∈ S, (actualLocalAnchorInput S B (by linarith) hunit j).variation.real univ) ≤ _
    at hRaw
  apply hRaw.trans
  calc
    _ ≤ (canonicalLocalAnchorPolynomial * B ^ 6 *
        exp (correctedLowBandCoercivityExponent * B)) *
        exp (scalarAnchorMeasureExponent * B) := by
      exact mul_le_mul
        (anchor_inverse_variation_coefficient_le B _ hB hInv) hMass
        measureReal_nonneg (by positivity)
    _ = canonicalLocalAnchorPolynomial * B ^ 6 *
        exp ((correctedLowBandCoercivityExponent + scalarAnchorMeasureExponent) * B) := by
      rw [mul_assoc, ← exp_add, add_mul]
    _ ≤ exp (canonicalLocalAnchorExponent * B) := by
      simpa only [canonicalLocalAnchorExponent, Nat.cast_ofNat, add_assoc] using
        polynomial_mul_exp_le_exp
        (A := canonicalLocalAnchorPolynomial) (B := B)
        (D := correctedLowBandCoercivityExponent + scalarAnchorMeasureExponent)
        canonicalLocalAnchorPolynomial_pos.le hB 6

/-- Total variation of the literal canonical threshold-one anchor is bounded
by one positive universal exponential rate. -/
theorem sum_totalVariation_canonicalLocalAnchorInput_le_exp (B : ℝ) (hB : 1 ≤ B) :
    (∑ j ∈ lowBandSpinSet B, (canonicalLocalAnchorInput B hB j).variation.real univ) ≤
      exp (canonicalLocalAnchorExponent * B) := by
  exact sum_totalVariation_actualLocalAnchorInput_le_exp (lowBandSpinSet B)
    ((zero_mem_lowBandSpinSet B).mpr (by linarith)) B hB
    (fun j hj => (mem_lowBandSpinSet B j).mp hj)
    (isUnit_correctedLowBandIdentityPlus_canonical B hB)

end GapFamily.Analytic
