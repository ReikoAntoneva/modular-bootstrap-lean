import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRemainderSeries

noncomputable section
namespace GapFamily.Analytic.PoincareFourierRemainder
open Set MeasureTheory

/-- An explicit absolute constant for the input-spin remainder on the central vertical line. -/
def fourierRemainderThresholdConstant : ℝ :=
  4 * Real.pi * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) + 1

theorem fourierRemainderThresholdConstant_pos : 0 < fourierRemainderThresholdConstant := by
  have ht : 0 ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ) :=
    tsum_nonneg (fun n => Real.rpow_nonneg (by positivity) _)
  unfold fourierRemainderThresholdConstant
  positivity

/-- The explicit majorant at real part one-half is independent of both output spin
and imaginary spectral parameter. -/
theorem norm_fourierRemainder_half_le {y : ℝ} (hy : 0 < y) (j J : ℤ)
    {s : ℂ} (hs : s.re = 1 / 2) :
    ‖fourierRemainder y j J s‖ ≤
      (4 * Real.pi * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) *
        |(J : ℝ)| / Real.sqrt y := by
  have h := norm_fourierRemainder_le hy j J (s := s) (by rw [hs]; norm_num)
  rw [hs] at h
  rw [show -2 * (1 / 2 : ℝ) - 1 = -2 by norm_num] at h
  have he : y ^ (-(1 / 2 : ℝ)) = (Real.sqrt y)⁻¹ := by
    rw [Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow]
  rw [he] at h
  convert h using 1
  ring

/-- A single positive constant works for every height, both spins and the whole
central vertical line. -/
theorem norm_fourierRemainder_half_le_constant {y : ℝ} (hy : 0 < y) (j J : ℤ)
    {s : ℂ} (hs : s.re = 1 / 2) :
    ‖fourierRemainder y j J s‖ ≤
      fourierRemainderThresholdConstant * |(J : ℝ)| / Real.sqrt y := by
  refine (norm_fourierRemainder_half_le hy j J hs).trans ?_
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg y)
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  unfold fourierRemainderThresholdConstant
  linarith

/-- In particular the actual remainder at s=1/2 has the required height decay. -/
theorem norm_fourierRemainder_threshold_le {y : ℝ} (hy : 0 < y) (j J : ℤ) :
    ‖fourierRemainder y j J (1 / 2)‖ ≤
      fourierRemainderThresholdConstant * |(J : ℝ)| / Real.sqrt y :=
  norm_fourierRemainder_half_le_constant hy j J (by norm_num)

end GapFamily.Analytic.PoincareFourierRemainder
