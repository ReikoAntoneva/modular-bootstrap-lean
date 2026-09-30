import GapFamily.Analytic.Poincare.Fourier.PoincareGammaGaussianTransform

noncomputable section

namespace GapFamily.Analytic.PoincareScalarFourier

open Set MeasureTheory PoincareFourierRemainder PoincareGammaGaussian

/-- The genuinely integrable zero-output-frequency central Fourier transform. -/
theorem integral_centralFourierKernel_zero_eq_gamma {y : ℝ} (hy : 0 < y)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    (∫ t : ℝ, centralFourierKernel y 0 s t) =
      (y : ℂ) ^ (1 - s) * (Real.sqrt Real.pi : ℂ) *
        Complex.Gamma (s - (1 / 2 : ℂ)) / Complex.Gamma s := by
  have hs' : 0 < (s - (1 / 2 : ℂ)).re := by
    norm_num
    linarith
  have hexp : s - (1 / 2 : ℂ) - 1 = s - (3 / 2 : ℂ) := by ring
  have hG : (∫ u : ℝ in Ioi 0,
      (u : ℂ) ^ (s - (3 / 2 : ℂ)) *
        Complex.exp (-((y ^ 2 : ℝ) : ℂ) * (u : ℂ))) =
      (1 / ((y ^ 2 : ℝ) : ℂ)) ^ (s - (1 / 2 : ℂ)) *
        Complex.Gamma (s - (1 / 2 : ℂ)) := by
    simpa only [hexp, neg_mul] using
      (Complex.integral_cpow_mul_exp_neg_mul_Ioi
        (a := s - (1 / 2 : ℂ)) hs' (sq_pos_of_pos hy))
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hsquare : ((y ^ 2 : ℝ) : ℂ) ^ (s - (1 / 2 : ℂ)) =
      (y : ℂ) ^ (2 * (s - (1 / 2 : ℂ))) := by
    simpa only [Real.rpow_two, Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hy.le (2 : ℝ) (s - (1 / 2 : ℂ))).symm
  have hpower : (y : ℂ) ^ s *
      (1 / ((y ^ 2 : ℝ) : ℂ)) ^ (s - (1 / 2 : ℂ)) =
        (y : ℂ) ^ (1 - s) := by
    rw [one_div, Complex.inv_cpow_ofReal_nonneg (sq_nonneg y), hsquare,
      ← Complex.cpow_neg, ← Complex.cpow_add _ _ hyc]
    congr 1
    ring
  rw [integral_centralFourierKernel_eq_mellin hy 0 hs]
  simp only [Int.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
    Complex.ofReal_zero, zero_div, sub_zero]
  rw [hG]
  calc
    _ = ((y : ℂ) ^ s * (1 / ((y ^ 2 : ℝ) : ℂ)) ^ (s - (1 / 2 : ℂ))) *
        (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s - (1 / 2 : ℂ)) /
          Complex.Gamma s := by ring
    _ = _ := by rw [hpower]

end GapFamily.Analytic.PoincareScalarFourier
