import GapFamily.Analytic.Kernel.LowBandThresholdFunctional
import GapFamily.Analytic.Foundation.ExponentialPolynomialBound

/-!
# Uniform smoothing threshold bound

The actual threshold mass becomes a bounded Hilbert functional after ordinary
kernel smoothing. Its bound is polynomial in the band width, hence controlled
by one universal exponential on bands of width at least one.
-/

noncomputable section

open Real

namespace GapFamily.Analytic

/-- A universal exponential rate for the smoothed threshold functional. -/
def correctedSmoothingThresholdExponent : ℝ := 300 * correctedKernelBound + 5

theorem correctedSmoothingThresholdExponent_pos :
    0 < correctedSmoothingThresholdExponent := by
  have := correctedKernelBound_pos
  unfold correctedSmoothingThresholdExponent
  positivity

/-- The ordinary threshold functional is bounded after actual kernel smoothing,
uniformly over all distinct physical spin families. -/
theorem norm_correctedSmoothingThresholdFunctional_le_polynomial
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B) :
    ‖correctedSmoothingThresholdFunctional J B (zero_le_one.trans hB)‖ ≤
      300 * correctedKernelBound * B ^ 5 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC := correctedKernelBound_pos.le
  have hcard := physicalLowBand_card_le J hJ hB hband
  have hs : sqrt (Fintype.card ι : ℝ) ≤ 5 * B := by
    exact (sqrt_le_sqrt hcard).trans (sqrt_le_self_iff.mpr (Or.inr (by linarith)))
  have hS := correctedSmoothingBound_le B hB
  have hS0 := correctedSmoothingBound_nonneg B hB0
  calc
    _ ≤ ‖lowBandThresholdFunctional J B‖ *
        ‖correctedKernelFiniteSmoothingOperator J J B hB0‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (3 * B) * ((Fintype.card ι : ℝ) *
        (correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ))) :=
      mul_le_mul (norm_lowBandThresholdFunctional_le_physical J B hB
        (fun i => (hband i).le))
        (norm_correctedKernelFiniteSmoothingOperator_le J J B hB0)
        (norm_nonneg _) (by positivity)
    _ ≤ (3 * B) * ((5 * B) * ((4 * correctedKernelBound * B ^ 2) * (5 * B))) := by
      gcongr
    _ = _ := by ring

/-- One positive universal exponent controls the norm of the actual smoothed
threshold mass, including its scalar reference-measure endpoint. -/
theorem norm_correctedSmoothingThresholdFunctional_le_exp
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B) :
    ‖correctedSmoothingThresholdFunctional J B (zero_le_one.trans hB)‖ ≤
      exp (correctedSmoothingThresholdExponent * B) := by
  apply (norm_correctedSmoothingThresholdFunctional_le_polynomial J hJ B hB hband).trans
  simpa only [correctedSmoothingThresholdExponent, zero_mul, exp_zero, mul_one,
    add_zero, Nat.cast_ofNat] using
    polynomial_mul_exp_le_exp (A := 300 * correctedKernelBound) (B := B) (D := 0)
      (mul_nonneg (by norm_num) correctedKernelBound_pos.le) hB 5

end GapFamily.Analytic
