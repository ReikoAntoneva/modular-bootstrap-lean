import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRemainderKernel

/-! The actual zero-input-phase term factors by its positive denominator, and
the ordinary full-line Fourier integral splits into central and remainder parts. -/

noncomputable section
namespace GapFamily.Analytic.PoincareFourierRemainder
open Set MeasureTheory PoincareFourierUnfold

/-- The zero-input-spin unrolled kernel has the exact negative denominator power.
This pointwise identity holds for every complex exponent. -/
theorem fourierKernel_zero_eq_factor_central {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j : ℤ) (s : ℂ) (t : ℝ) :
    fourierKernel c y j 0 s t =
      (c : ℂ) ^ (-(2 * s)) * centralFourierKernel y j s t := by
  have hd : 0 < t ^ 2 + y ^ 2 := by positivity
  have hsquare : ((c ^ 2 : ℝ) : ℂ) ^ s = (c : ℂ) ^ (2 * s) := by
    simpa only [Real.rpow_two, Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hc.le (2 : ℝ) s).symm
  have hbase : ((y / (c ^ 2 * (t ^ 2 + y ^ 2)) : ℝ) : ℂ) ^ s =
      ((y / (t ^ 2 + y ^ 2) : ℝ) : ℂ) ^ s / ((c ^ 2 : ℝ) : ℂ) ^ s := by
    rw [show y / (c ^ 2 * (t ^ 2 + y ^ 2)) =
      (y / (t ^ 2 + y ^ 2)) / c ^ 2 by rw [div_div, mul_comm (t ^ 2 + y ^ 2)]]
    simpa only [Complex.ofReal_div] using
      Complex.div_cpow_ofReal_nonneg (div_nonneg hy.le hd.le) (sq_nonneg c) s
  simp only [fourierKernel, centralFourierKernel, neg_zero, cuspFourierMode]
  simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [hbase, hsquare, Complex.cpow_neg]
  ring

/-- The central kernel is the actual denominator-one, zero-input-spin kernel,
so its full-line integral is genuine on the half-plane Re(s) > 1/2. -/
theorem integrable_centralFourierKernel {y : ℝ} (hy : 0 < y) (j : ℤ)
    {s : ℂ} (hs : 1 / 2 < s.re) : Integrable (centralFourierKernel y j s) := by
  have he : fourierKernel 1 y j 0 s = centralFourierKernel y j s := by
    funext t
    simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using
      fourierKernel_zero_eq_factor_central zero_lt_one hy j s t
  rw [← he]
  exact integrable_fourierKernel zero_lt_one hy j 0 hs

/-- On the original absolute-integrability half-plane, phase subtraction is
the difference of two genuinely integrable unrolled kernels. -/
theorem integrable_fourierRemainderKernel_of_half {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (fourierRemainderKernel c y j J s) := by
  have he : fourierRemainderKernel c y j J s =
      fun t => fourierKernel c y j J s t - fourierKernel c y j 0 s t := by
    funext t
    exact fourierRemainderKernel_eq_sub c y j J s t
  rw [he]
  exact (integrable_fourierKernel hc hy j J hs).sub
    (integrable_fourierKernel hc hy j 0 hs)

/-- Split the actual ordinary integral into the exact central denominator factor
and the actual phase-subtracted remainder integral. -/
theorem integral_fourierKernel_eq_central_add_remainder {c y : ℝ}
    (hc : 0 < c) (hy : 0 < y) (j J : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) :
    (∫ t : ℝ, fourierKernel c y j J s t) =
      (c : ℂ) ^ (-(2 * s)) * (∫ t : ℝ, centralFourierKernel y j s t) +
        ∫ t : ℝ, fourierRemainderKernel c y j J s t := by
  have he : fourierKernel c y j J s = fun t =>
      fourierKernel c y j 0 s t + fourierRemainderKernel c y j J s t := by
    funext t
    rw [fourierRemainderKernel_eq_sub]
    ring
  rw [he, integral_add (integrable_fourierKernel hc hy j 0 hs)
    (integrable_fourierRemainderKernel_of_half hc hy j J hs)]
  simp_rw [fourierKernel_zero_eq_factor_central hc hy j s]
  rw [integral_const_mul]

end GapFamily.Analytic.PoincareFourierRemainder
