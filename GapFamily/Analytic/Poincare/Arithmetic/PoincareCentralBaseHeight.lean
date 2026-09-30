import GapFamily.Analytic.Poincare.PoincareFrequencyHeight
import GapFamily.Analytic.Bessel.BesselFourierNormalization

noncomputable section
namespace GapFamily.Analytic.PoincareCentralZeta
open PoincareCentralFactor

/-- The actual frequency-dependent observation height never exceeds one. -/
theorem frequencyHeight_le_one (N : ℤ) : frequencyHeight N ≤ 1 := by
  unfold frequencyHeight
  apply (div_le_iff₀ (show 0 < 1 + |(N : ℝ)| by positivity)).mpr
  linarith [abs_nonneg (N : ℝ)]

/-- The literal direct threshold term obeys the reciprocal-square-root height bound. -/
theorem norm_directThreshold_le_inv_sqrt {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1)
    (N : ℤ) :
    ‖(if N = 1 then (y : ℂ) ^ (1 / 2 : ℂ) else 0)‖ ≤ 1 / Real.sqrt y := by
  split_ifs
  · rw [← BesselCoshOrder.ofReal_sqrt_eq_cpow_half hy.le,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg y)]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hy)).mpr
    simpa only [Real.mul_self_sqrt hy.le] using hy1
  · simp only [norm_zero]
    positivity

/-- The two actual square-root height factors combine to a single linear frequency weight. -/
theorem frequencyHeight_sqrt_product (A D : ℝ) (N : ℤ) :
    (A / Real.sqrt (frequencyHeight N)) * (D * Real.sqrt (1 + |(N : ℝ)|)) =
      A * D * (1 + |(N : ℝ)|) := by
  rw [div_eq_mul_inv, inv_sqrt_frequencyHeight]
  calc
    _ = A * D * (Real.sqrt (1 + |(N : ℝ)|)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (show 0 ≤ 1 + |(N : ℝ)| by positivity)]

end GapFamily.Analytic.PoincareCentralZeta
