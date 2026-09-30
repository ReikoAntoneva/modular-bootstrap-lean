import GapFamily.Analytic.Kernel.FullKernelResponse

/-!
# Polynomial coefficient for input-strip growth

The imaginary input radius controls the exponential, while the full input
radius and fixed input spin enter an explicit polynomial coefficient. The
same coefficient absorbs both the Hilbert and ordinary mass moments.
-/

noncomputable section

open Real

namespace GapFamily.Analytic

/-- The energy coefficient for an input column on a complex rectangle. -/
def inputColumnStripCoefficient (jin : ℤ) (B R r : ℝ) : ℝ :=
  centralKernelBound * |(jin : ℝ)| +
    16 * π ^ 2 * (R ^ 2 + 2 * |(jin : ℝ)|) * exp (4 * π * r * sqrt B)

theorem inputColumnStripCoefficient_nonneg (jin : ℤ) (B R r : ℝ) :
    0 ≤ inputColumnStripCoefficient jin B R r := by
  have := centralKernelBound_pos
  unfold inputColumnStripCoefficient
  positivity

/-- A positive polynomial coefficient also absorbs the scalar rank term. -/
def inputColumnStripPolynomial (jin : ℤ) (R : ℝ) : ℝ :=
  centralKernelBound * |(jin : ℝ)| + 16 * π ^ 2 * (R ^ 2 + 2 * |(jin : ℝ)|) +
    12 * R + 1

theorem inputColumnStripPolynomial_pos (jin : ℤ) (R : ℝ) (hR : 0 ≤ R) :
    0 < inputColumnStripPolynomial jin R := by
  have := centralKernelBound_pos
  unfold inputColumnStripPolynomial
  positivity

/-- The central coefficient is absorbed into the nonnegative strip exponent. -/
theorem inputColumnStripCoefficient_le (jin : ℤ) (B R r : ℝ) (hr : 0 ≤ r) :
    inputColumnStripCoefficient jin B R r ≤
      (centralKernelBound * |(jin : ℝ)| + 16 * π ^ 2 * (R ^ 2 + 2 * |(jin : ℝ)|)) *
        exp (4 * π * r * sqrt B) := by
  have hExp : 1 ≤ exp (4 * π * r * sqrt B) := one_le_exp_iff.mpr (by positivity)
  have hC : 0 ≤ centralKernelBound * |(jin : ℝ)| :=
    mul_nonneg centralKernelBound_pos.le (abs_nonneg _)
  unfold inputColumnStripCoefficient
  calc
    _ ≤ centralKernelBound * |(jin : ℝ)| * exp (4 * π * r * sqrt B) +
        16 * π ^ 2 * (R ^ 2 + 2 * |(jin : ℝ)|) * exp (4 * π * r * sqrt B) :=
      add_le_add (le_mul_of_one_le_right hC hExp) le_rfl
    _ = _ := by ring

/-- Ordinary low-band energy moments preserve the input-strip exponential. -/
theorem inputColumnStripL1Coefficient_le (jin : ℤ) (B R r : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hr : 0 ≤ r) :
    inputColumnStripCoefficient jin B R r * B + 12 * R * (B + 2 * sqrt B) ≤
      inputColumnStripPolynomial jin R * (B + 2 * sqrt B) * exp (4 * π * r * sqrt B) := by
  let C := centralKernelBound * |(jin : ℝ)| +
    16 * π ^ 2 * (R ^ 2 + 2 * |(jin : ℝ)|)
  have hC : 0 ≤ C := by
    have := centralKernelBound_pos
    dsimp [C]
    positivity
  have hExp : 1 ≤ exp (4 * π * r * sqrt B) := one_le_exp_iff.mpr (by positivity)
  have hBstep : B ≤ B + 2 * sqrt B := le_add_of_nonneg_right (by positivity)
  have hPoly : C + 12 * R ≤ inputColumnStripPolynomial jin R := by
    dsimp [C, inputColumnStripPolynomial]
    linarith
  calc
    _ ≤ (C * exp (4 * π * r * sqrt B)) * B +
        (12 * R * (B + 2 * sqrt B)) * exp (4 * π * r * sqrt B) :=
      add_le_add (mul_le_mul_of_nonneg_right (inputColumnStripCoefficient_le jin B R r hr) hB)
        (le_mul_of_one_le_right (by positivity) hExp)
    _ ≤ (C * exp (4 * π * r * sqrt B)) * (B + 2 * sqrt B) +
        (12 * R * (B + 2 * sqrt B)) * exp (4 * π * r * sqrt B) :=
      add_le_add (mul_le_mul_of_nonneg_left hBstep
        (mul_nonneg hC (exp_pos _).le)) le_rfl
    _ = (C + 12 * R) * (B + 2 * sqrt B) * exp (4 * π * r * sqrt B) := by ring
    _ ≤ _ := by gcongr

/-- The Hilbert moment coefficient is bounded by the same strip expression. -/
theorem inputColumnStripHilbertCoefficient_le (jin : ℤ) (B R r : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hr : 0 ≤ r) :
    inputColumnStripCoefficient jin B R r * B + 12 * R * sqrt B ≤
      inputColumnStripPolynomial jin R * (B + 2 * sqrt B) * exp (4 * π * r * sqrt B) := by
  apply le_trans ?_ (inputColumnStripL1Coefficient_le jin B R r hB hR hr)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith [sqrt_nonneg B]

end GapFamily.Analytic
