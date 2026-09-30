import GapFamily.Analytic.Poincare.Fourier.PoincareScalarThresholdIdentification
import GapFamily.Analytic.Poincare.Fourier.PoincareScalarFourierAsymptotic
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRemainderThreshold

noncomputable section
namespace GapFamily.Analytic.PoincareScalarFourier
open Set Filter MeasureTheory CuspFourierCutoff
open PoincareFourierContinuation PoincareFourierRemainder
open PoincareEnergyFourier
open scoped Topology

/-- The actual scalar coefficient at arbitrary complex energy retains the exact divisor term,
with both ordinary convergent corrections left intact. -/
theorem generalThresholdFourierCoefficient_zero_eq_divisor_add_corrections
    (y : ℝ) (hy : 0 < y) (E : ℂ) (J : ℤ) (hJ : J ≠ 0) :
    generalThresholdFourierCoefficient y hy E 0 J =
      (Real.sqrt y : ℂ) * (2 * (J.natAbs.divisors.card : ℂ)) +
        fourierRemainder y 0 J (1 / 2 : ℂ) +
          ∑' n : ℕ, kloostermanSum 0 J n *
            ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E 0 J (1 / 2 : ℂ) t := by
  rw [generalThresholdFourierCoefficient_eq_base_add_kloosterman,
    thresholdFourierCoefficient_zero_eq_divisor_add_remainder y hy J hJ,
    energyFourierDirect, ite_eq_right (Ne.symm hJ), add_zero]

/-- The actual phase-subtracted remainder cannot change any normalized scalar cusp limit. -/
theorem fourierRemainder_div_sqrt_tendsto_zero (j J : ℤ) :
    Tendsto (fun y : ℝ => fourierRemainder y j J (1 / 2 : ℂ) / (Real.sqrt y : ℂ))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm'
    (a := fun y : ℝ => fourierRemainderThresholdConstant * |(J : ℝ)| / y)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg y)]
    calc
      _ ≤ (fourierRemainderThresholdConstant * |(J : ℝ)| / Real.sqrt y) / Real.sqrt y :=
        div_le_div_of_nonneg_right (norm_fourierRemainder_threshold_le hy j J)
          (Real.sqrt_nonneg y)
      _ = _ := by rw [div_div, Real.mul_self_sqrt hy.le]
  · exact tendsto_id.const_div_atTop _

/-- For each fixed nonzero input spin, the actual scalar Fourier cusp limit is exactly
2*d(|J|), independently of the nonnegative real input energy. No atom measure is asserted. -/
theorem nonzeroScalarThresholdFourier_div_sqrt_tendsto_divisor
    {E : ℝ} (hE : 0 ≤ E) (J : ℤ) (hJ : J ≠ 0) :
    Tendsto (fun y : ℝ => if hy : 0 < y then
      generalThresholdFourierCoefficient y hy (E : ℂ) 0 J / (Real.sqrt y : ℂ)
      else 0) atTop (𝓝 (2 * (J.natAbs.divisors.card : ℂ))) := by
  have h := ((tendsto_const_nhds (x := 2 * (J.natAbs.divisors.card : ℂ))).add
    (fourierRemainder_div_sqrt_tendsto_zero 0 J)).add
    (energyFourier_denominator_sum_div_sqrt_tendsto_zero hE 0 J)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hs : (Real.sqrt y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hy).ne'
  rw [dite_eq_left hy,
    generalThresholdFourierCoefficient_zero_eq_divisor_add_corrections y hy (E : ℂ) J hJ,
    add_div, add_div, mul_div_cancel_left₀ _ hs]

end GapFamily.Analytic.PoincareScalarFourier
