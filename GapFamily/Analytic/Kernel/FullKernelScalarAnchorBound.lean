import GapFamily.Analytic.Kernel.FullKernelScalarAnchorResponse
import GapFamily.Analytic.Kernel.FullKernelCoercivityBound
import GapFamily.Analytic.Kernel.FullKernelSmoothingThresholdBound
import GapFamily.Analytic.Foundation.ThresholdAnchorNonvanishing

/-! Uniform exponential bounds for the actual scalar anchor response.
The threshold mass is controlled in the ordinary L1 space, while the inverse
and smoothing contribution use their proved physical operator bounds. -/
noncomputable section
namespace GapFamily.Analytic
open Real Set

/-- Fixed-disk exponential control of the actual inverse scalar column. -/
theorem norm_correctedScalarInverseColumn_le_exp_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (hP : (correctedLowBandIdentityPlus J (4 * B)).IsPositive)
    (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedScalarInverseColumn J B (by linarith) z‖ ≤
      exp ((correctedLowBandCoercivityExponent + correctedResponseDiskExponent R) * B) := by
  calc
    _ ≤ ‖correctedLowBandInverse J B‖ * exp (correctedResponseDiskExponent R * B) :=
      norm_correctedScalarInverseColumn_le J hJ B hB hband R hR z hz
    _ ≤ exp (correctedLowBandCoercivityExponent * B) *
        exp (correctedResponseDiskExponent R * B) :=
      mul_le_mul_of_nonneg_right
        (norm_correctedLowBandInverse_le_exp_of_positive J hJ B hB hband hP) (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

private theorem one_add_band_exp_add_exp_le (L M B : ℝ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hB : 1 ≤ B) :
    1 + 3 * B * exp (L * B) + exp (M * B) ≤ exp ((L + M + 6) * B) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have h1 : 1 ≤ exp ((L + M) * B) := one_le_exp_iff.mpr (by positivity)
  have hL' : exp (L * B) ≤ exp ((L + M) * B) := by
    apply exp_le_exp.mpr
    nlinarith
  have hM' : exp (M * B) ≤ exp ((L + M) * B) := by
    apply exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ 1 + 3 * B * exp ((L + M) * B) + exp ((L + M) * B) := by gcongr
    _ ≤ (5 * B) * exp ((L + M) * B) := by nlinarith [exp_pos ((L + M) * B)]
    _ ≤ _ := by
      convert polynomial_mul_exp_le_exp (A := (5 : ℝ)) (D := L + M) (by norm_num) hB 1
        using 1 <;> simp only [pow_one, Nat.cast_one]
      congr 1
      ring

/-- A rate depending only on the chosen square-root disk. -/
def scalarAnchorResponseDiskExponent (R : ℝ) : ℝ :=
  scalarColumnL1DiskCardExponent R +
    (correctedSmoothingThresholdExponent +
      (correctedLowBandCoercivityExponent + correctedResponseDiskExponent R)) + 6

theorem scalarAnchorResponseDiskExponent_pos (R : ℝ) (hR : 0 ≤ R) :
    0 < scalarAnchorResponseDiskExponent R := by
  unfold scalarAnchorResponseDiskExponent
  have := scalarColumnL1DiskCardExponent_pos R hR
  have := correctedSmoothingThresholdExponent_pos
  have := correctedLowBandCoercivityExponent_pos
  have := correctedResponseDiskExponent_pos R hR
  positivity

/-- The complete actual scalar anchor response has a uniform fixed-disk
exponential bound, conditional only on the enlarged physical positivity. -/
theorem norm_scalarAnchorResponseHol_le_exp_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (hP : (correctedLowBandIdentityPlus J (4 * B)).IsPositive)
    (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖scalarAnchorResponseHol J B (by linarith) z‖ ≤
      exp (scalarAnchorResponseDiskExponent R * B) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hL1 := norm_correctedScalarColumnL1_le_exp J hJ B hB hband R hR z hz
  have hInv := norm_correctedScalarInverseColumn_le_exp_of_positive J hJ B hB hband hP R hR z hz
  have hMass : ‖lowBandThresholdFunctional J B (correctedScalarColumnL1 J B hB0 z)‖ ≤
      3 * B * exp (scalarColumnL1DiskCardExponent R * B) := by
    apply ((lowBandThresholdFunctional J B).le_opNorm _).trans
    exact mul_le_mul (norm_lowBandThresholdFunctional_le_physical J B hB
      (fun i => (hband i).le)) hL1 (norm_nonneg _) (by positivity)
  have hSmooth : ‖correctedSmoothingThresholdFunctional J B hB0
      (correctedScalarInverseColumn J B hB0 z)‖ ≤
      exp ((correctedSmoothingThresholdExponent +
        (correctedLowBandCoercivityExponent + correctedResponseDiskExponent R)) * B) := by
    calc
      _ ≤ ‖correctedSmoothingThresholdFunctional J B hB0‖ *
          ‖correctedScalarInverseColumn J B hB0 z‖ :=
        (correctedSmoothingThresholdFunctional J B hB0).le_opNorm _
      _ ≤ exp (correctedSmoothingThresholdExponent * B) *
          exp ((correctedLowBandCoercivityExponent + correctedResponseDiskExponent R) * B) :=
        mul_le_mul (norm_correctedSmoothingThresholdFunctional_le_exp J hJ B hB hband)
          hInv (norm_nonneg _) (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  calc
    _ ≤ 1 + (‖lowBandThresholdFunctional J B (correctedScalarColumnL1 J B hB0 z)‖ +
        ‖correctedSmoothingThresholdFunctional J B hB0
          (correctedScalarInverseColumn J B hB0 z)‖) := by
      let a := lowBandThresholdFunctional J B (correctedScalarColumnL1 J B hB0 z)
      let b := correctedSmoothingThresholdFunctional J B hB0
        (correctedScalarInverseColumn J B hB0 z)
      change ‖(-1 : ℂ) - (a - b)‖ ≤ 1 + (‖a‖ + ‖b‖)
      calc
        _ ≤ ‖(-1 : ℂ)‖ + ‖a - b‖ := norm_sub_le _ _
        _ = 1 + ‖a - b‖ := by rw [norm_neg, norm_one]
        _ ≤ _ := by linarith only [norm_sub_le a b]
    _ ≤ 1 + 3 * B * exp (scalarColumnL1DiskCardExponent R * B) +
        exp ((correctedSmoothingThresholdExponent +
          (correctedLowBandCoercivityExponent + correctedResponseDiskExponent R)) * B) := by
      linarith
    _ ≤ _ := one_add_band_exp_add_exp_le _ _ B
      (scalarColumnL1DiskCardExponent_pos R hR).le
      (by have := correctedSmoothingThresholdExponent_pos
          have := correctedLowBandCoercivityExponent_pos
          have := correctedResponseDiskExponent_pos R hR
          positivity) hB

/-- Every fixed disk admits one positive rate for all physical bands. -/
theorem exists_scalarAnchorResponse_fixedDisk_bound (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (J : ι → ℤ)
      (_hJ : Function.Injective J) (B : ℝ) (hB : 1 ≤ B)
      (_hband : ∀ i, |(J i : ℝ)| < B)
      (_hP : (correctedLowBandIdentityPlus J (4 * B)).IsPositive)
      (z : ℂ), ‖z‖ ≤ R →
      ‖scalarAnchorResponseHol J B (by linarith) z‖ ≤ exp (C * B) := by
  refine ⟨scalarAnchorResponseDiskExponent R, scalarAnchorResponseDiskExponent_pos R hR, ?_⟩
  intro ι _ J hJ B hB hband hP z hz
  exact norm_scalarAnchorResponseHol_le_exp_of_positive J hJ B hB hband hP R hR z hz

/-- Quantitative nonvanishing of the actual physical high-band response. -/
theorem scalarAnchorResponseSquareMass_lower_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (hP : (correctedLowBandIdentityPlus J (4 * B)).IsPositive) :
    1 / (10000 * exp (scalarAnchorResponseDiskExponent 16384 * B)) ^ 2 ≤
      scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith)) := by
  have hBpos : 0 < B := by linarith
  have hunit := isUnit_correctedLowBandIdentityPlus_of_positive J hJ B hB hband hP
  exact scalarAnchorSquareMass_lower_of_entire
    (scalarAnchorResponseHol J B hBpos.le)
    (exp (scalarAnchorResponseDiskExponent 16384 * B)) B
    (scalarAnchorResponsePhysical J B hBpos.le) (exp_pos _).le hBpos
    (differentiable_scalarAnchorResponseHol J B hBpos.le)
    (scalarAnchorResponseHol_zero J B hBpos.le)
    (fun z hz => norm_scalarAnchorResponseHol_le_exp_of_positive
      J hJ B hB hband hP 16384 (by norm_num) z hz)
    (continuous_scalarAnchorResponsePhysical J B hBpos.le).continuousOn
    (fun t ht => scalarAnchorResponseHol_eq_physical J B hBpos hunit t
      ((sqrt_nonneg 2).trans ht.1))

/-- A universal normalization rate for the fixed propagation disk. -/
def scalarAnchorResponseMassExponent : ℝ :=
  2 * (10000 + scalarAnchorResponseDiskExponent 16384)

theorem scalarAnchorResponseMassExponent_pos : 0 < scalarAnchorResponseMassExponent := by
  unfold scalarAnchorResponseMassExponent
  have := scalarAnchorResponseDiskExponent_pos 16384 (by norm_num)
  positivity

/-- The actual normalizing square mass has a band-linear exponential lower bound. -/
theorem exp_neg_le_scalarAnchorResponseSquareMass_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (hP : (correctedLowBandIdentityPlus J (4 * B)).IsPositive) :
    exp (-scalarAnchorResponseMassExponent * B) ≤
      scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith)) := by
  have hcoeff : 10000 * exp (scalarAnchorResponseDiskExponent 16384 * B) ≤
      exp ((10000 + scalarAnchorResponseDiskExponent 16384) * B) := by
    simpa only [pow_zero, mul_one, Nat.cast_zero, add_zero] using
      polynomial_mul_exp_le_exp (A := (10000 : ℝ))
        (D := scalarAnchorResponseDiskExponent 16384) (by norm_num) hB 0
  have hsq := pow_le_pow_left₀ (by positivity :
    0 ≤ 10000 * exp (scalarAnchorResponseDiskExponent 16384 * B)) hcoeff 2
  have hden : (10000 * exp (scalarAnchorResponseDiskExponent 16384 * B)) ^ 2 ≤
      exp (scalarAnchorResponseMassExponent * B) := by
    refine hsq.trans_eq ?_
    rw [← exp_nat_mul]
    congr 1
    unfold scalarAnchorResponseMassExponent
    norm_num
    ring
  have hinv := (inv_le_inv₀ (exp_pos (scalarAnchorResponseMassExponent * B))
    (by positivity : 0 < (10000 * exp (scalarAnchorResponseDiskExponent 16384 * B)) ^ 2)).mpr hden
  rw [← exp_neg] at hinv
  have hlower := scalarAnchorResponseSquareMass_lower_of_positive J hJ B hB hband hP
  apply le_trans ?_ hlower
  simpa only [neg_mul, one_div] using hinv

/-- The actual high-band normalization factor has a uniform exponential bound. -/
theorem scalarAnchorResponseSquareMass_inv_le_exp_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (hP : (correctedLowBandIdentityPlus J (4 * B)).IsPositive) :
    (scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith)))⁻¹ ≤
      exp (scalarAnchorResponseMassExponent * B) := by
  have hlower := exp_neg_le_scalarAnchorResponseSquareMass_of_positive J hJ B hB hband hP
  have hpos := lt_of_lt_of_le (exp_pos _) hlower
  have hinv := (inv_le_inv₀ hpos (exp_pos _)).mpr hlower
  simpa only [← exp_neg, neg_mul, neg_neg] using hinv

end GapFamily.Analytic
