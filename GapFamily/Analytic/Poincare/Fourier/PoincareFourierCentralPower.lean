import GapFamily.Analytic.Poincare.Fourier.PoincareFourierCentralFactor

noncomputable section
namespace GapFamily.Analytic.PoincareFourierRemainder
open MeasureTheory Set

/-- The positive-height central kernel factors into its literal exterior height power. -/
theorem centralFourierKernel_eq_height_mul {y : ℝ} (hy : 0 < y)
    (j : ℤ) (s : ℂ) (t : ℝ) :
    centralFourierKernel y j s t = (y : ℂ) ^ s *
      ((((t ^ 2 + y ^ 2 : ℝ) : ℂ) ^ (-s)) * cuspFourierMode (-j) t) := by
  have hd : 0 < t ^ 2 + y ^ 2 := by positivity
  unfold centralFourierKernel
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hy.le hd.le,
    Complex.cpow_neg, div_eq_mul_inv, mul_assoc]

/-- The literal rational-power Fourier integrand is ordinarily integrable on Re(s)>1/2. -/
theorem integrable_rationalFourierKernel {y : ℝ} (hy : 0 < y)
    (j : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (fun t : ℝ =>
      (((t ^ 2 + y ^ 2 : ℝ) : ℂ) ^ (-s)) * cuspFourierMode (-j) t) := by
  have hn : (y : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  have hc := integrable_centralFourierKernel hy j hs
  have he : centralFourierKernel y j s = fun t : ℝ => (y : ℂ) ^ s *
      ((((t ^ 2 + y ^ 2 : ℝ) : ℂ) ^ (-s)) * cuspFourierMode (-j) t) :=
    funext (centralFourierKernel_eq_height_mul hy j s)
  rw [he] at hc
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hn) _).mp hc

/-- Algebraic integral factorization; ordinary convergence on Re(s)>1/2 is supplied above. -/
theorem integral_centralFourierKernel_eq_height_mul {y : ℝ} (hy : 0 < y)
    (j : ℤ) (s : ℂ) :
    (∫ t : ℝ, centralFourierKernel y j s t) = (y : ℂ) ^ s *
      ∫ t : ℝ, (((t ^ 2 + y ^ 2 : ℝ) : ℂ) ^ (-s)) * cuspFourierMode (-j) t := by
  simp_rw [centralFourierKernel_eq_height_mul hy j s]
  exact integral_const_mul _ _

end GapFamily.Analytic.PoincareFourierRemainder
