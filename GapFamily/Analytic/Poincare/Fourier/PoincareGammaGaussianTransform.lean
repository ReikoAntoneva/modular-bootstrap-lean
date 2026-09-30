import GapFamily.Analytic.Poincare.Fourier.PoincareGammaRate
import GapFamily.Analytic.Poincare.Fourier.PoincareGammaGaussianIntegrable
import GapFamily.Analytic.Poincare.Fourier.PoincareGammaGaussianSlice

/-! Genuine Gamma--Gaussian Fubini reduction of the ordinary central Fourier transform. -/
noncomputable section
namespace GapFamily.Analytic.PoincareGammaGaussian
open Set MeasureTheory PoincareFourierRemainder

/-- The positive Mellin integral produced by Fubini is genuinely integrable,
including zero output spin, throughout Re s>1/2. -/
theorem integrableOn_centralMellinKernel {y : ℝ} (hy : 0 < y) (j : ℤ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - (3 / 2 : ℂ)) *
      Complex.exp (-((y ^ 2 : ℝ) : ℂ) * (u : ℂ) -
        ((Real.pi ^ 2 * (j : ℝ) ^ 2 : ℝ) : ℂ) / (u : ℂ))) (Ioi 0) := by
  have hf := (integrable_gammaFourierKernel hy j hs).integral_prod_right
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  apply (hf.const_mul (Real.sqrt Real.pi : ℂ)⁻¹).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [integral_gammaFourierKernel_gaussian y j s hu]
  simp only [← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

/-- Fubini is applied to the proved integrable joint Gamma--Gaussian kernel. -/
theorem gamma_mul_integral_centralFourierKernel_eq_mellin
    {y : ℝ} (hy : 0 < y) (j : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) :
    Complex.Gamma s * (∫ t : ℝ, centralFourierKernel y j s t) =
      (y : ℂ) ^ s * (Real.sqrt Real.pi : ℂ) *
        ∫ u : ℝ in Ioi 0, (u : ℂ) ^ (s - (3 / 2 : ℂ)) *
          Complex.exp (-((y ^ 2 : ℝ) : ℂ) * (u : ℂ) -
            ((Real.pi ^ 2 * (j : ℝ) ^ 2 : ℝ) : ℂ) / (u : ℂ)) := by
  have hs0 : 0 < s.re := by linarith
  calc
    _ = ∫ t : ℝ, Complex.Gamma s * centralFourierKernel y j s t :=
      (integral_const_mul _ _).symm
    _ = ∫ t : ℝ, (y : ℂ) ^ s * ∫ u : ℝ in Ioi 0, gammaFourierKernel y j s t u := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact gamma_mul_centralFourierKernel_eq hy j hs0 t
    _ = (y : ℂ) ^ s * ∫ t : ℝ, ∫ u : ℝ in Ioi 0, gammaFourierKernel y j s t u :=
      integral_const_mul _ _
    _ = (y : ℂ) ^ s * ∫ u : ℝ in Ioi 0, ∫ t : ℝ, gammaFourierKernel y j s t u := by
      rw [integral_integral_swap (integrable_gammaFourierKernel hy j hs)]
    _ = (y : ℂ) ^ s * ∫ u : ℝ in Ioi 0,
        (Real.sqrt Real.pi : ℂ) * ((u : ℂ) ^ (s - (3 / 2 : ℂ)) *
          Complex.exp (-((y ^ 2 : ℝ) : ℂ) * (u : ℂ) -
            ((Real.pi ^ 2 * (j : ℝ) ^ 2 : ℝ) : ℂ) / (u : ℂ))) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      simpa only [mul_assoc] using integral_gammaFourierKernel_gaussian y j s hu
    _ = _ := by rw [integral_const_mul]; ring

/-- The literal central ordinary Fourier integral reduces to its positive Mellin
integral with a=y² and b=π²j². No boundary-line integrability is claimed. -/
theorem integral_centralFourierKernel_eq_mellin
    {y : ℝ} (hy : 0 < y) (j : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) :
    (∫ t : ℝ, centralFourierKernel y j s t) =
      (y : ℂ) ^ s / Complex.Gamma s * (Real.sqrt Real.pi : ℂ) *
        ∫ u : ℝ in Ioi 0, (u : ℂ) ^ (s - (3 / 2 : ℂ)) *
          Complex.exp (-((y ^ 2 : ℝ) : ℂ) * (u : ℂ) -
            ((Real.pi ^ 2 * (j : ℝ) ^ 2 : ℝ) : ℂ) / (u : ℂ)) := by
  have hΓ := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  apply mul_left_cancel₀ hΓ
  rw [gamma_mul_integral_centralFourierKernel_eq_mellin hy j hs]
  field_simp

end GapFamily.Analytic.PoincareGammaGaussian
