import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileCore

/-! Literal real-coordinate algebra for the fixed-denominator Fourier unfolding. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourierUnfold
open Complex

/-- Translating by d/c centers the quadratic denominator at the origin. -/
theorem normSq_affine_row (c d x y : ℝ) (hc : c ≠ 0) :
    Complex.normSq ((c : ℂ) * Complex.mk x y + (d : ℂ)) =
      c ^ 2 * ((x + d / c) ^ 2 + y ^ 2) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  field_simp [hc]

/-- The real inverse-denominator correction has the exact unrolled-kernel form. -/
theorem re_inv_affine_row (c d x y : ℝ) (hc : 0 < c) (hy : 0 < y) :
    (1 / ((c : ℂ) * ((c : ℂ) * Complex.mk x y + (d : ℂ)))).re =
      (x + d / c) / (c ^ 2 * ((x + d / c) ^ 2 + y ^ 2)) := by
  have hq : 0 < (x + d / c) ^ 2 + y ^ 2 := by positivity
  have hp : 0 < (c * (c * x + d)) ^ 2 + (c * (c * y)) ^ 2 := by positivity
  simp only [Complex.div_re, Complex.one_re, Complex.one_im,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, sub_zero, add_zero]
  field_simp [hc.ne', hq.ne', hp.ne']
  ring

/-- Output-frequency translation produces the positive rational residue phase. -/
theorem cuspFourierMode_shift_split (j : ℤ) (x r : ℝ) :
    cuspFourierMode (-j) x = cuspFourierMode j r * cuspFourierMode (-j) (x + r) := by
  unfold cuspFourierMode
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Negating the argument is the same as negating the integer Fourier index. -/
theorem cuspFourierMode_neg_argument (J : ℤ) (x : ℝ) :
    cuspFourierMode J (-x) = cuspFourierMode (-J) x := by
  unfold cuspFourierMode
  congr 1
  push_cast
  ring

end GapFamily.Analytic.PoincareFourierUnfold
