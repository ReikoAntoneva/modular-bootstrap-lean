import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileCore
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

noncomputable section
namespace GapFamily.Analytic.PoincareGammaGaussian
open Set MeasureTheory Filter
open scoped Topology

/-- The literal Gamma parameter integrand for the ordinary horizontal Fourier coefficient. -/
def gammaFourierKernel (y : ℝ) (j : ℤ) (s : ℂ) (t u : ℝ) : ℂ :=
  (u : ℂ) ^ (s - 1) * Complex.exp (-((t ^ 2 + y ^ 2 : ℝ) : ℂ) * (u : ℂ)) *
    cuspFourierMode (-j) t

private theorem continuousOn_gammaFourierKernel (y : ℝ) (j : ℤ) (s : ℂ) :
    ContinuousOn (fun p : ℝ × ℝ => gammaFourierKernel y j s p.1 p.2)
      (univ ×ˢ Ioi 0) := by
  have hp : ContinuousOn (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (s - 1)) (univ ×ˢ Ioi 0) :=
    ((Complex.continuous_ofReal.comp continuous_snd).continuousOn).cpow_const
      (fun p hp => Or.inl hp.2)
  exact (hp.mul (by fun_prop)).mul
    (((contDiff_cuspFourierMode (-j)).continuous.comp continuous_fst).continuousOn)

private theorem aestronglyMeasurable_gammaFourierKernel (y : ℝ) (j : ℤ) (s : ℂ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => gammaFourierKernel y j s p.1 p.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have h := (continuousOn_gammaFourierKernel y j s).aestronglyMeasurable
    (μ := volume.prod volume) (MeasurableSet.univ.prod measurableSet_Ioi)
  simpa only [← Measure.prod_restrict, Measure.restrict_univ] using h

/-- The positive Gamma parameter removes every complex branch and Fourier norm factor. -/
theorem norm_gammaFourierKernel (y : ℝ) (j : ℤ) (s : ℂ) (t u : ℝ) (hu : 0 < u) :
    ‖gammaFourierKernel y j s t u‖ =
      u ^ (s.re - 1) * Real.exp (-((t ^ 2 + y ^ 2) * u)) := by
  rw [gammaFourierKernel, norm_mul, norm_mul, norm_cuspFourierMode, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simp only [Complex.sub_re, Complex.one_re, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, neg_mul]

private theorem integrableOn_gammaFourierNorm {y : ℝ} (hy : 0 < y) (j : ℤ)
    {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    Integrable (fun u : ℝ => ‖gammaFourierKernel y j s t u‖) (volume.restrict (Ioi 0)) := by
  have hr : 0 < t ^ 2 + y ^ 2 := by positivity
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s.re - 1)
    (p := 1) (b := t ^ 2 + y ^ 2) (by linarith) zero_lt_one hr
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_gammaFourierKernel y j s t u hu]
  simp only [Real.rpow_one, neg_mul]

/-- The actual inner norm integral is the Gamma-scaled quadratic envelope. -/
theorem integral_norm_gammaFourierKernel {y : ℝ} (hy : 0 < y) (j : ℤ)
    {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    (∫ u : ℝ in Ioi 0, ‖gammaFourierKernel y j s t u‖) =
      Real.Gamma s.re * (t ^ 2 + y ^ 2) ^ (-s.re) := by
  have hr : 0 < t ^ 2 + y ^ 2 := by positivity
  calc
    _ = ∫ u : ℝ in Ioi 0, u ^ (s.re - 1) * Real.exp (-((t ^ 2 + y ^ 2) * u)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact norm_gammaFourierKernel y j s t u hu
    _ = _ := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr,
        one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
      exact mul_comm _ _


open MeasureTheory Filter

private theorem quadratic_rpow_eq_height_scaled {y : ℝ} (hy : 0 < y) (t r : ℝ) :
    (t ^ 2 + y ^ 2) ^ r = (y ^ 2) ^ r * (1 + (t / y) ^ 2) ^ r := by
  have hbase : t ^ 2 + y ^ 2 = y ^ 2 * (1 + (t / y) ^ 2) := by
    field_simp [hy.ne']
    ring
  rw [hbase, Real.mul_rpow (sq_nonneg y) (by positivity)]

private theorem integrable_quadratic_rpow {y σ : ℝ} (hy : 0 < y) (hσ : 1 / 2 < σ) :
    Integrable (fun t : ℝ => (t ^ 2 + y ^ 2) ^ (-σ)) volume := by
  have hone : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-σ)) volume := by
    have hj := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * σ)
      (by simpa using (show (1 : ℝ) < 2 * σ by linarith))
    convert hj using 1
    ext t
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  apply ((hone.comp_div hy.ne').const_mul ((y ^ 2) ^ (-σ))).congr
  exact Eventually.of_forall fun t => (quadratic_rpow_eq_height_scaled hy t (-σ)).symm

/-- Genuine Fubini integrability of the literal Gamma–Gaussian Fourier kernel. -/
theorem integrable_gammaFourierKernel {y : ℝ} (hy : 0 < y) (j : ℤ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (fun p : ℝ × ℝ => gammaFourierKernel y j s p.1 p.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hs0 : 0 < s.re := lt_trans (by norm_num) hs
  have hm := aestronglyMeasurable_gammaFourierKernel y j s
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [hm.prodMk_left] with t ht
    exact (integrable_norm_iff ht).mp (integrableOn_gammaFourierNorm hy j hs0 t)
  · have h := (integrable_quadratic_rpow hy hs).const_mul (Real.Gamma s.re)
    apply h.congr
    filter_upwards with t
    exact (integral_norm_gammaFourierKernel hy j hs0 t).symm

/-- The actual ordinary double integral may be swapped, using the proved product integrability. -/
theorem integral_integral_gammaFourierKernel_swap {y : ℝ} (hy : 0 < y) (j : ℤ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    (∫ t : ℝ, ∫ u : ℝ in Ioi 0, gammaFourierKernel y j s t u) =
      ∫ u : ℝ in Ioi 0, ∫ t : ℝ, gammaFourierKernel y j s t u :=
  integral_integral_swap (integrable_gammaFourierKernel hy j hs)

end GapFamily.Analytic.PoincareGammaGaussian
