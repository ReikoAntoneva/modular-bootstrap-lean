import GapFamily.Analytic.Poincare.Repair.PoincareAnchorExteriorOutput
import GapFamily.Analytic.Poincare.Repair.PoincareCanonicalAnchorBound
import GapFamily.Analytic.Kernel.FullKernelSignedResponseBound

/-! The actual exterior anchor has an ordinary pointwise bound, including its
literal high-band density. The exponential rate is uniform in the physical
output spin and energy; energy contributes only a linear factor. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Real

/-- The canonical anchor's actual signed mass is uniformly exponential. -/
theorem signedSeedMass_canonicalLocalAnchorInput_le_exp (B : ℝ) (hB : 1 ≤ B) :
    signedSeedMass (fun J : lowBandSpinSet B => canonicalLocalAnchorInput B hB J) ≤
      exp (canonicalLocalAnchorExponent * B) := by
  calc
    _ = ∑ j ∈ lowBandSpinSet B, (canonicalLocalAnchorInput B hB j).variation.real univ :=
      Finset.sum_coe_sort (lowBandSpinSet B)
        (fun j : ℤ => (canonicalLocalAnchorInput B hB j).variation.real univ)
    _ ≤ _ := sum_totalVariation_canonicalLocalAnchorInput_le_exp B hB

/-- The signed kernel response of the canonical anchor has linear exterior-energy growth. -/
theorem norm_correctedSignedResponse_canonicalAnchor_le (B : ℝ) (hB : 1 ≤ B)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    ‖correctedSignedResponse (fun J : lowBandSpinSet B => canonicalLocalAnchorInput B hB J)
      Subtype.val j e‖ ≤
      (6 * correctedKernelBound * B * e) * exp (canonicalLocalAnchorExponent * B) := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hC := correctedKernelBound_pos
  calc
    _ ≤ signedSeedMass (fun J : lowBandSpinSet B => canonicalLocalAnchorInput B hB J) *
        (6 * correctedKernelBound * B * e) :=
      norm_correctedSignedResponse_le_exterior
        (fun J : lowBandSpinSet B => canonicalLocalAnchorInput B hB J)
        (fun J : lowBandSpinSet B => (J : ℤ)) j B hB
        (fun J => canonicalLocalAnchorInput_physicalSupport B hB J) e he hBe
    _ ≤ exp (canonicalLocalAnchorExponent * B) * (6 * correctedKernelBound * B * e) :=
      mul_le_mul_of_nonneg_right (signedSeedMass_canonicalLocalAnchorInput_le_exp B hB)
        (by positivity)
    _ = _ := mul_comm _ _

/-- The direct scalar numerator and full signed response are both present in
this bound for the literal actual exterior anchor. -/
theorem abs_canonicalAnchorExteriorNumerator_le (B : ℝ) (hB : 1 ≤ B)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    |canonicalAnchorExteriorNumerator B hB j e| ≤
      exp (scalarAnchorMeasureExponent * B) +
        (6 * correctedKernelBound * B * e) * exp (canonicalLocalAnchorExponent * B) := by
  have hDirect : |(if j = 0 then scalarAnchorNumerator B
      (scalarAnchorResponsePhysical (fun J : lowBandSpinSet B => (J : ℤ)) B
        (zero_le_one.trans hB)) e else 0)| ≤ exp (scalarAnchorMeasureExponent * B) := by
    split_ifs
    · exact abs_scalarAnchorNumerator_actual_le_exp _ (lowBandSpin_injective B)
        B hB (lowBandSpin_physical B) e
    · simpa only [abs_zero] using (exp_pos (scalarAnchorMeasureExponent * B)).le
  unfold canonicalAnchorExteriorNumerator
  apply (abs_add_le _ _).trans
  exact add_le_add hDirect
    ((Complex.abs_re_le_norm _).trans
      (norm_correctedSignedResponse_canonicalAnchor_le B hB j e he hBe))

/-- One universal rate controls the complete exterior anchor. -/
def canonicalAnchorExteriorExponent : ℝ :=
  (1 + 6 * correctedKernelBound) +
    (scalarAnchorMeasureExponent + canonicalLocalAnchorExponent) + 1

theorem canonicalAnchorExteriorExponent_pos : 0 < canonicalAnchorExteriorExponent := by
  unfold canonicalAnchorExteriorExponent
  have := correctedKernelBound_pos
  have := scalarAnchorMeasureExponent_pos
  have := canonicalLocalAnchorExponent_pos
  positivity

/-- The exterior anchor bound, uniform in every physical exterior
output energy and spin, with no inverse or positivity premise. -/
theorem abs_canonicalAnchorExteriorNumerator_le_energy_mul_exp
    (B : ℝ) (hB : 1 ≤ B) (j : ℤ) (e : ℝ)
    (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    |canonicalAnchorExteriorNumerator B hB j e| ≤
      e * exp (canonicalAnchorExteriorExponent * B) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have he1 : 1 ≤ e := hB.trans hBe
  have he0 : 0 ≤ e := zero_le_one.trans he1
  have hC := correctedKernelBound_pos
  have hA := scalarAnchorMeasureExponent_pos
  have hT := canonicalLocalAnchorExponent_pos
  have hleft : exp (scalarAnchorMeasureExponent * B) ≤
      exp ((scalarAnchorMeasureExponent + canonicalLocalAnchorExponent) * B) := by
    apply exp_le_exp.mpr
    nlinarith
  have hright : exp (canonicalLocalAnchorExponent * B) ≤
      exp ((scalarAnchorMeasureExponent + canonicalLocalAnchorExponent) * B) := by
    apply exp_le_exp.mpr
    nlinarith
  apply (abs_canonicalAnchorExteriorNumerator_le B hB j e he hBe).trans
  calc
    _ ≤ exp ((scalarAnchorMeasureExponent + canonicalLocalAnchorExponent) * B) +
        (6 * correctedKernelBound * B * e) *
          exp ((scalarAnchorMeasureExponent + canonicalLocalAnchorExponent) * B) := by gcongr
    _ = (1 + 6 * correctedKernelBound * B * e) *
        exp ((scalarAnchorMeasureExponent + canonicalLocalAnchorExponent) * B) := by ring
    _ ≤ ((1 + 6 * correctedKernelBound) * B * e) *
        exp ((scalarAnchorMeasureExponent + canonicalLocalAnchorExponent) * B) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      nlinarith [one_le_mul_of_one_le_of_one_le hB he1]
    _ = e * ((1 + 6 * correctedKernelBound) * B ^ 1 *
        exp ((scalarAnchorMeasureExponent + canonicalLocalAnchorExponent) * B)) := by ring
    _ ≤ e * exp (canonicalAnchorExteriorExponent * B) := by
      apply mul_le_mul_of_nonneg_left _ he0
      simpa only [canonicalAnchorExteriorExponent, Nat.cast_one] using
        polynomial_mul_exp_le_exp (A := 1 + 6 * correctedKernelBound)
          (D := scalarAnchorMeasureExponent + canonicalLocalAnchorExponent)
          (by positivity) hB 1

end GapFamily.Analytic
