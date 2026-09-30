import GapFamily.Analytic.Kernel.FullKernelPropagationLossBound

/-!
# Uniform exponential coercivity and inverse bounds

The explicit coefficient obtained by propagation is bounded below by one
global exponential rate. The actual inverse has the reciprocal exponential
bound. Enlarged-band positivity is kept explicit in these operator conclusions
and is discharged in `FullKernelInverse`.
-/

noncomputable section

open Real

namespace GapFamily.Analytic

/-- A single global rate for physical low-band coercivity and its inverse. -/
def correctedLowBandCoercivityExponent : ℝ :=
  2 * (12 + correctedIdentityPlusExponent + correctedPropagationLossExponent)

theorem correctedLowBandCoercivityExponent_pos : 0 < correctedLowBandCoercivityExponent := by
  unfold correctedLowBandCoercivityExponent
  have := correctedIdentityPlusExponent_pos
  have := correctedPropagationLossExponent_pos
  positivity

/-- The denominator of the explicit coefficient has a uniform exponential bound. -/
theorem correctedLowBandCoercivityDenominator_le_exp
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    {b : ℝ} (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b) :
    4 * (‖correctedLowBandIdentityPlus J b‖ + correctedPropagationLoss J b + 1) ≤
      exp ((12 + correctedIdentityPlusExponent + correctedPropagationLossExponent) * b) := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hA := correctedIdentityPlusExponent_pos
  have hL := correctedPropagationLossExponent_pos
  have hP : ‖correctedLowBandIdentityPlus J b‖ ≤
      exp ((correctedIdentityPlusExponent + correctedPropagationLossExponent) * b) := by
    refine (norm_correctedLowBandIdentityPlus_le_exp J hJ hb hband).trans ?_
    apply exp_le_exp.mpr
    nlinarith
  have hK : correctedPropagationLoss J b ≤
      exp ((correctedIdentityPlusExponent + correctedPropagationLossExponent) * b) := by
    refine (correctedPropagationLoss_le_exp J hJ hb hband).trans ?_
    apply exp_le_exp.mpr
    nlinarith
  have h1 : 1 ≤ exp ((correctedIdentityPlusExponent + correctedPropagationLossExponent) * b) :=
    one_le_exp_iff.mpr (by positivity)
  calc
    _ ≤ 12 * exp ((correctedIdentityPlusExponent + correctedPropagationLossExponent) * b) := by
      linarith
    _ ≤ _ := by
      convert polynomial_mul_exp_le_exp (A := (12 : ℝ))
        (D := correctedIdentityPlusExponent + correctedPropagationLossExponent)
        (by norm_num) hb 0 using 1 <;> simp only [pow_zero, mul_one, Nat.cast_zero, add_zero]
      ring_nf

/-- The reciprocal of the actual coefficient grows at most exponentially,
before making any positivity assumption on the operator. -/
theorem correctedLowBandCoercivityConstant_inv_le_exp
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    {b : ℝ} (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b) :
    (correctedLowBandCoercivityConstant J b)⁻¹ ≤ exp (correctedLowBandCoercivityExponent * b) := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hD : 0 ≤ 4 * (‖correctedLowBandIdentityPlus J b‖ + correctedPropagationLoss J b + 1) := by
    have := correctedPropagationLoss_nonneg J hb0
    positivity
  have hpow := pow_le_pow_left₀ hD (correctedLowBandCoercivityDenominator_le_exp J hJ hb hband) 2
  change ((4 * (‖correctedLowBandIdentityPlus J b‖ + correctedPropagationLoss J b + 1))⁻¹ ^ 2)⁻¹ ≤ _
  rw [inv_pow, inv_inv]
  refine hpow.trans_eq ?_
  rw [← exp_nat_mul]
  congr 1
  unfold correctedLowBandCoercivityExponent
  ring

/-- Uniform lower bound for the exact coefficient produced by the actual
response, observation, and propagation estimates. -/
theorem exp_neg_le_correctedLowBandCoercivityConstant
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    {b : ℝ} (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b) :
    exp (-correctedLowBandCoercivityExponent * b) ≤ correctedLowBandCoercivityConstant J b := by
  have hc := correctedLowBandCoercivityConstant_pos J (zero_le_one.trans hb)
  have h := (inv_le_inv₀ (exp_pos (correctedLowBandCoercivityExponent * b))
    (inv_pos.mpr hc)).mpr (correctedLowBandCoercivityConstant_inv_le_exp J hJ hb hband)
  rw [inv_inv, ← exp_neg] at h
  simpa only [neg_mul] using h

/-- A single exponential rate gives actual physical low-band coercivity,
conditional only on positivity of the enlarged physical compression. -/
theorem correctedLowBandIdentityPlus_exp_coercive_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (b : ℝ) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b)
    (hP : (correctedLowBandIdentityPlus J (4 * b)).IsPositive)
    (f : LowBandHilbert J b) :
    exp (-correctedLowBandCoercivityExponent * b) * ‖f‖ ^ 2 ≤
      (inner ℂ f (correctedLowBandIdentityPlus J b f)).re :=
  (mul_le_mul_of_nonneg_right (exp_neg_le_correctedLowBandCoercivityConstant J hJ hb hband)
    (sq_nonneg _)).trans
    (correctedLowBandIdentityPlus_coercive_of_positive J hJ b hb hband hP f)

/-- The actual inverse in the bounded-operator algebra has one global
exponential norm bound on physical spin families. -/
theorem norm_correctedLowBandInverse_le_exp_of_positive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (b : ℝ) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b)
    (hP : (correctedLowBandIdentityPlus J (4 * b)).IsPositive) :
    ‖correctedLowBandInverse J b‖ ≤ exp (correctedLowBandCoercivityExponent * b) :=
  (norm_correctedLowBandInverse_le_of_positive J hJ b hb hband hP).trans
    (correctedLowBandCoercivityConstant_inv_le_exp J hJ hb hband)

end GapFamily.Analytic
