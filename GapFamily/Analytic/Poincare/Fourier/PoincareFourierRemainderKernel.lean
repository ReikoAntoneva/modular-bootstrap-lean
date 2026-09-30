import GapFamily.Analytic.Poincare.Fourier.PoincareFourierKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The actual phase-subtracted unrolled Fourier kernel. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourierRemainder
open Set MeasureTheory PoincareFourierUnfold

/-- Remove exactly the inner input-spin phase's constant term. -/
def fourierRemainderKernel (c y : ℝ) (j J : ℤ) (s : ℂ) (t : ℝ) : ℂ :=
  ((y / (c ^ 2 * (t ^ 2 + y ^ 2)) : ℝ) : ℂ) ^ s *
    (cuspFourierMode (-J) (t / (c ^ 2 * (t ^ 2 + y ^ 2))) - 1) *
      cuspFourierMode (-j) t

/-- The central ordinary Fourier factor has denominator one and no inner phase. -/
def centralFourierKernel (y : ℝ) (j : ℤ) (s : ℂ) (t : ℝ) : ℂ :=
  ((y / (t ^ 2 + y ^ 2) : ℝ) : ℂ) ^ s * cuspFourierMode (-j) t

theorem fourierRemainderKernel_eq_sub (c y : ℝ) (j J : ℤ) (s : ℂ) (t : ℝ) :
    fourierRemainderKernel c y j J s t =
      fourierKernel c y j J s t - fourierKernel c y j 0 s t := by
  simp only [fourierRemainderKernel, fourierKernel, neg_zero, cuspFourierMode]
  simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  ring

/-- The input Fourier phase changes by at most its real angular displacement. -/
theorem norm_cuspFourierMode_sub_one_le (J : ℤ) (u : ℝ) :
    ‖cuspFourierMode J u - 1‖ ≤ 2 * Real.pi * |(J : ℝ)| * |u| := by
  have he : cuspFourierMode J u = Complex.exp (Complex.I * ((2 * Real.pi * (J : ℝ) * u : ℝ) : ℂ)) := by
    unfold cuspFourierMode
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_of_pos zero_lt_two]
  calc
    2 * |Real.sin ((2 * Real.pi * (J : ℝ) * u) / 2)| ≤
        2 * |(2 * Real.pi * (J : ℝ) * u) / 2| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs zero_le_two
    _ = _ := by rw [abs_div, abs_mul, abs_mul, abs_mul,
                    abs_of_pos zero_lt_two, abs_of_pos Real.pi_pos]; ring

theorem continuous_fourierRemainderKernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) (s : ℂ) : Continuous (fourierRemainderKernel c y j J s) := by
  have he : fourierRemainderKernel c y j J s =
      fun t => fourierKernel c y j J s t - fourierKernel c y j 0 s t := by
    funext t; exact fourierRemainderKernel_eq_sub c y j J s t
  rw [he]
  exact (continuous_fourierKernel hc hy j J s).sub (continuous_fourierKernel hc hy j 0 s)

/-- The literal phase subtraction supplies an extra denominator and a factor |t|. -/
theorem norm_fourierRemainderKernel_le {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) (s : ℂ) (t : ℝ) :
    ‖fourierRemainderKernel c y j J s t‖ ≤
      (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ s.re *
        (2 * Real.pi * |(J : ℝ)| * (|t| / (c ^ 2 * (t ^ 2 + y ^ 2)))) := by
  rw [fourierRemainderKernel, norm_mul, norm_mul, norm_cuspFourierMode, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < y / (c ^ 2 * (t ^ 2 + y ^ 2)))]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
  have h := norm_cuspFourierMode_sub_one_le (-J) (t / (c ^ 2 * (t ^ 2 + y ^ 2)))
  simpa only [Int.cast_neg, abs_neg, abs_div, abs_of_pos (by positivity : 0 < c ^ 2 * (t ^ 2 + y ^ 2))] using h

end GapFamily.Analytic.PoincareFourierRemainder
