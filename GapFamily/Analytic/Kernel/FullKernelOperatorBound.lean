import GapFamily.Analytic.Kernel.FullKernelOperatorMomentBound
import GapFamily.Analytic.Foundation.ExponentialPolynomialBound

/-!
# Uniform bounds for the actual identity-plus-kernel operator

The ordinary low-band energy moments give a finite-row operator bound.
The number of distinct physical integer rows is at most `5 B`, so the
bound grows cubically in the band width. The same global exponential
rate controls the original band and its fourfold enlargement.
-/

noncomputable section

open Real

namespace GapFamily.Analytic

/-- An explicit positive bound from ordinary low-band moments. -/
def correctedIdentityPlusBound {ι : Type*} [Fintype ι] (_J : ι → ℤ) (B : ℝ) : ℝ :=
  1 + correctedKernelBound * (|B| ^ 2 + |B|) * (Fintype.card ι : ℝ)

theorem one_le_correctedIdentityPlusBound {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) : 1 ≤ correctedIdentityPlusBound J B := by
  unfold correctedIdentityPlusBound
  have := correctedKernelBound_pos
  exact le_add_of_nonneg_right (by positivity)

theorem correctedIdentityPlusBound_pos {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) : 0 < correctedIdentityPlusBound J B :=
  zero_lt_one.trans_le (one_le_correctedIdentityPlusBound J B)

/-- The bound controls the actual bounded identity-plus-kernel operator. -/
theorem norm_correctedLowBandIdentityPlus_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ‖correctedLowBandIdentityPlus J B‖ ≤ correctedIdentityPlusBound J B := by
  change ‖ContinuousLinearMap.id ℂ (LowBandHilbert J B) + correctedLowBandOperator J B‖ ≤ _
  calc
    _ ≤ ‖ContinuousLinearMap.id ℂ (LowBandHilbert J B)‖ + ‖correctedLowBandOperator J B‖ :=
      norm_add_le _ _
    _ ≤ 1 + correctedKernelBound * (B ^ 2 + B) * (Fintype.card ι : ℝ) :=
      add_le_add ContinuousLinearMap.norm_id_le (norm_correctedLowBandOperator_le_moment J B hB)
    _ = correctedIdentityPlusBound J B := by
      simp only [correctedIdentityPlusBound, abs_of_nonneg hB]

/-- One global coefficient controls the cubic operator growth. -/
def correctedIdentityPlusPolynomial : ℝ := 1 + 10 * correctedKernelBound

theorem correctedIdentityPlusPolynomial_pos : 0 < correctedIdentityPlusPolynomial := by
  unfold correctedIdentityPlusPolynomial
  have := correctedKernelBound_pos
  positivity

theorem correctedIdentityPlusBound_physical_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) {B : ℝ} (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) :
    correctedIdentityPlusBound J B ≤ correctedIdentityPlusPolynomial * B ^ 3 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC := correctedKernelBound_pos.le
  have hcard := physicalLowBand_card_le J hJ hB hband
  have hpoly : B ^ 2 + B ≤ 2 * B ^ 2 := by nlinarith
  have hpow : 1 ≤ B ^ 3 := one_le_pow₀ hB
  unfold correctedIdentityPlusBound
  rw [abs_of_nonneg hB0]
  calc
    _ ≤ 1 + correctedKernelBound * (2 * B ^ 2) * (5 * B) := by
      gcongr
    _ ≤ B ^ 3 + correctedKernelBound * (2 * B ^ 2) * (5 * B) :=
      add_le_add_left hpow _
    _ = correctedIdentityPlusPolynomial * B ^ 3 := by
      unfold correctedIdentityPlusPolynomial
      ring

/-- The same original physical row set can be used on the enlarged band. -/
theorem correctedIdentityPlusBound_fourfold_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) {b : ℝ} (hb : 1 ≤ b)
    (hband : ∀ i, |(J i : ℝ)| < b) :
    correctedIdentityPlusBound J (4 * b) ≤
      (64 * correctedIdentityPlusPolynomial) * b ^ 3 := by
  have h := correctedIdentityPlusBound_physical_le J hJ
    (show 1 ≤ 4 * b by linarith)
    (fun i => (hband i).trans_le (by linarith : b ≤ 4 * b))
  convert h using 1 <;> ring

/-- A single positive exponential rate absorbs both cubic bounds. -/
def correctedIdentityPlusExponent : ℝ := 64 * correctedIdentityPlusPolynomial + 3

theorem correctedIdentityPlusExponent_pos : 0 < correctedIdentityPlusExponent := by
  unfold correctedIdentityPlusExponent
  have := correctedIdentityPlusPolynomial_pos
  positivity

theorem correctedIdentityPlusBound_le_exp {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) {b : ℝ} (hb : 1 ≤ b)
    (hband : ∀ i, |(J i : ℝ)| < b) :
    correctedIdentityPlusBound J b ≤ exp (correctedIdentityPlusExponent * b) := by
  have hpos := correctedIdentityPlusPolynomial_pos
  refine (correctedIdentityPlusBound_physical_le J hJ hb hband).trans ?_
  calc
    _ ≤ (64 * correctedIdentityPlusPolynomial) * b ^ 3 := by
      have := correctedIdentityPlusPolynomial_pos
      have hb0 : 0 ≤ b := zero_le_one.trans hb
      nlinarith [mul_nonneg correctedIdentityPlusPolynomial_pos.le (pow_nonneg hb0 3)]
    _ ≤ _ := by
      simpa only [zero_mul, exp_zero, mul_one, add_zero, Nat.cast_ofNat,
        correctedIdentityPlusExponent] using
        (polynomial_mul_exp_le_exp (A := 64 * correctedIdentityPlusPolynomial)
          (D := 0) (by positivity) hb 3)

theorem correctedIdentityPlusBound_fourfold_le_exp {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) {b : ℝ} (hb : 1 ≤ b)
    (hband : ∀ i, |(J i : ℝ)| < b) :
    correctedIdentityPlusBound J (4 * b) ≤ exp (correctedIdentityPlusExponent * b) := by
  refine (correctedIdentityPlusBound_fourfold_le J hJ hb hband).trans ?_
  have := correctedIdentityPlusPolynomial_pos
  simpa only [zero_mul, exp_zero, mul_one, add_zero, Nat.cast_ofNat,
    correctedIdentityPlusExponent] using
    (polynomial_mul_exp_le_exp (A := 64 * correctedIdentityPlusPolynomial)
      (D := 0) (by positivity) hb 3)

theorem norm_correctedLowBandIdentityPlus_le_polynomial {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) {b : ℝ} (hb : 1 ≤ b)
    (hband : ∀ i, |(J i : ℝ)| < b) :
    ‖correctedLowBandIdentityPlus J b‖ ≤ correctedIdentityPlusPolynomial * b ^ 3 :=
  (norm_correctedLowBandIdentityPlus_le J b (zero_le_one.trans hb)).trans
    (correctedIdentityPlusBound_physical_le J hJ hb hband)

theorem norm_correctedLowBandIdentityPlus_fourfold_le_polynomial {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) {b : ℝ} (hb : 1 ≤ b)
    (hband : ∀ i, |(J i : ℝ)| < b) :
    ‖correctedLowBandIdentityPlus J (4 * b)‖ ≤
      (64 * correctedIdentityPlusPolynomial) * b ^ 3 :=
  (norm_correctedLowBandIdentityPlus_le J (4 * b) (by linarith)).trans
    (correctedIdentityPlusBound_fourfold_le J hJ hb hband)

theorem norm_correctedLowBandIdentityPlus_le_exp {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) {b : ℝ} (hb : 1 ≤ b)
    (hband : ∀ i, |(J i : ℝ)| < b) :
    ‖correctedLowBandIdentityPlus J b‖ ≤ exp (correctedIdentityPlusExponent * b) :=
  (norm_correctedLowBandIdentityPlus_le J b (zero_le_one.trans hb)).trans
    (correctedIdentityPlusBound_le_exp J hJ hb hband)

theorem norm_correctedLowBandIdentityPlus_fourfold_le_exp {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) {b : ℝ} (hb : 1 ≤ b)
    (hband : ∀ i, |(J i : ℝ)| < b) :
    ‖correctedLowBandIdentityPlus J (4 * b)‖ ≤ exp (correctedIdentityPlusExponent * b) :=
  (norm_correctedLowBandIdentityPlus_le J (4 * b) (by linarith)).trans
    (correctedIdentityPlusBound_fourfold_le_exp J hJ hb hband)

end GapFamily.Analytic
