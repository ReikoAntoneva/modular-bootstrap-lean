import GapFamily.Analytic.Kernel.FullKernelInputInverseColumn
import GapFamily.Analytic.Kernel.FullKernelInputColumnStripBound

/-! Sharp input-strip estimates survive the actual low-band inverse and the
ordinary threshold mass. Only the imaginary width enters the exponential.
-/

noncomputable section

open Real

namespace GapFamily.Analytic

variable {ι : Type*} [Fintype ι]

/-- The common majorant of the actual Hilbert and ordinary L1 input columns. -/
def inputColumnStripSize (n : ℕ) (jin : ℤ) (B R r : ℝ) : ℝ :=
  (n : ℝ) * inputColumnStripPolynomial jin R * (B + 2 * sqrt B) *
    exp (4 * π * r * sqrt B)

theorem inputColumnStripSize_nonneg (n : ℕ) (jin : ℤ) (B R r : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) : 0 ≤ inputColumnStripSize n jin B R r := by
  have := (inputColumnStripPolynomial_pos jin R hR).le
  unfold inputColumnStripSize
  positivity

theorem norm_correctedInputInverseColumn_strip_le (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (z : ℂ) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖correctedInputInverseColumn J B hB jin z‖ ≤
      ‖correctedLowBandInverse J B‖ * inputColumnStripSize (Fintype.card ι) jin B R r := by
  exact ((correctedLowBandInverse J B).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left
      (norm_correctedInputColumn_strip_le J B hB jin R r hR hr z hz him)
      (norm_nonneg _))

/-- Ordinary mass of the inverse column uses bounded smoothing, with the same
imaginary-width exponential as the input column. -/
theorem norm_correctedInputInverseColumnL1_strip_le (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (z : ℂ) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖correctedInputInverseColumnL1 J B hB jin z‖ ≤
      (1 + (Fintype.card ι : ℝ) *
        (correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ)) *
          ‖correctedLowBandInverse J B‖) *
            inputColumnStripSize (Fintype.card ι) jin B R r := by
  have hs : 0 ≤ (Fintype.card ι : ℝ) *
      (correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ)) := by
    have := correctedSmoothingBound_nonneg B hB
    positivity
  calc
    _ ≤ ‖correctedInputColumnL1 J B hB jin z‖ +
        (Fintype.card ι : ℝ) * (correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ)) *
          ‖correctedInputInverseColumn J B hB jin z‖ :=
      norm_correctedInputInverseColumnL1_le J B hB jin z
    _ ≤ inputColumnStripSize (Fintype.card ι) jin B R r +
        (Fintype.card ι : ℝ) * (correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ)) *
          (‖correctedLowBandInverse J B‖ *
            inputColumnStripSize (Fintype.card ι) jin B R r) :=
      add_le_add (norm_correctedInputColumnL1_strip_le J B hB jin R r hR hr z hz him)
        (mul_le_mul_of_nonneg_left
          (norm_correctedInputInverseColumn_strip_le J B hB jin R r hR hr z hz him) hs)
    _ = _ := by ring

/-- The threshold coefficient is the actual weighted ordinary inverse mass,
bounded without a mass functional on the scalar Hilbert space. -/
theorem norm_correctedInputInverseThreshold_strip_le (J : ι → ℤ) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| ≤ B) (jin : ℤ) (R r : ℝ)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖correctedInputInverseThreshold J B (by linarith) jin z‖ ≤
      3 * B * (1 + (Fintype.card ι : ℝ) *
        (correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ)) *
          ‖correctedLowBandInverse J B‖) *
            inputColumnStripSize (Fintype.card ι) jin B R r := by
  rw [correctedInputInverseThreshold_eq_L1]
  calc
    _ ≤ ‖lowBandThresholdFunctional J B‖ *
        ‖correctedInputInverseColumnL1 J B (by linarith) jin z‖ :=
      (lowBandThresholdFunctional J B).le_opNorm _
    _ ≤ (3 * B) * ((1 + (Fintype.card ι : ℝ) *
        (correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ)) *
          ‖correctedLowBandInverse J B‖) *
            inputColumnStripSize (Fintype.card ι) jin B R r) :=
      mul_le_mul (norm_lowBandThresholdFunctional_le_physical J B hB hband)
        (norm_correctedInputInverseColumnL1_strip_le J B (by linarith)
          jin R r hR hr z hz him) (norm_nonneg _) (by linarith)
    _ = _ := by ring

end GapFamily.Analytic
