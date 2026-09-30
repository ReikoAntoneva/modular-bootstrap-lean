import GapFamily.Analytic.Spatial.SpatialPointKernelBasic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Point spatial Laplace factorization

The actual point kernel at `s = 1/2` is represented by two ordinary, absolutely
integrable Gamma–Laplace factors. The proof uses the complex Gaussian integral
and the substitution `t = x²`. The module also fixes the exact same-parameter
normalization `C_s`, including `C_(1/2) = 1`, and records the elementary `s = 1`
exponential factorization.

These are point identities. The light-cone change of variables, integer-frequency
periodization, same-parameter orbit identity, and continuation of the resulting
energy pairing remain separate steps.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open MeasureTheory Set
open scoped ComplexConjugate

/-- The same-parameter spatial Fourier–Laplace normalization. -/
def spatialLaplaceConstant (s : ℝ) : ℝ :=
  2 ^ (2 * s - 1) * Real.pi ^ (2 * s) / Real.Gamma s ^ 2

theorem spatialLaplaceConstant_one_half : spatialLaplaceConstant (1 / 2) = 1 := by
  unfold spatialLaplaceConstant
  norm_num [Real.Gamma_one_half_eq, Real.sq_sqrt Real.pi_pos.le, Real.pi_ne_zero]

theorem spatialLaplaceConstant_one : spatialLaplaceConstant 1 = 2 * Real.pi ^ 2 := by
  norm_num [spatialLaplaceConstant, Real.Gamma_one]

/-- The two decaying light-cone factors before the real-frequency change of variables. -/
def pointLaplaceRate (z w : ℂ) : ℂ :=
  2 * Real.pi * ((z.im + w.im : ℝ) + Complex.I * (z.re - w.re : ℝ))

theorem pointLaplaceRate_re_pos {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    0 < (pointLaplaceRate z w).re := by
  simp [pointLaplaceRate, Complex.mul_re, Real.pi_pos, add_pos hz hw]

theorem integrableOn_pointLaplaceFactor {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (fun t : ℝ => Complex.exp (-pointLaplaceRate z w * t)) (Ioi 0) := by
  apply integrableOn_exp_mul_complex_Ioi
  simpa using pointLaplaceRate_re_pos hz hw

theorem integral_pointLaplaceFactor {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-pointLaplaceRate z w * t)) =
      (pointLaplaceRate z w)⁻¹ := by
  rw [integral_exp_mul_complex_Ioi (by simpa using pointLaplaceRate_re_pos hz hw)]
  simp

theorem pointKernel_one_eq_double_laplace {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel 1 z w =
      (4 * Real.pi ^ 2 * z.im * w.im : ℂ) *
        (∫ t : ℝ in Ioi 0, Complex.exp (-pointLaplaceRate z w * t)) *
        (∫ t : ℝ in Ioi 0, Complex.exp (-pointLaplaceRate w z * t)) := by
  rw [integral_pointLaplaceFactor hz hw, integral_pointLaplaceFactor hw hz]
  have hr : pointLaplaceRate z w ≠ 0 := by
    intro h
    have := pointLaplaceRate_re_pos hz hw
    rw [h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hr' : pointLaplaceRate w z ≠ 0 := by
    intro h
    have := pointLaplaceRate_re_pos hw hz
    rw [h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hp : (pointParameter z w : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pointParameter_pos hz hw).ne'
  rw [pointKernel, Complex.cpow_neg_one]
  have hparam := pointParameter_eq_normSq_sub_conj hz hw
  rw [hparam] at hp ⊢
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat] at hp ⊢
  have hn : (Complex.normSq (z - conj w) : ℂ) ≠ 0 := by
    intro h
    simp [h] at hp
  rw [inv_div]
  field_simp [hr, hr', hn]
  simp only [pointLaplaceRate, Complex.ofReal_add, Complex.ofReal_sub]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, sub_neg_eq_add, Complex.ofReal_add, Complex.ofReal_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem pointLaplaceRate_conj (z w : ℂ) :
    pointLaplaceRate w z = conj (pointLaplaceRate z w) := by
  simp only [pointLaplaceRate, map_mul, map_add, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_add, Complex.ofReal_sub, map_sub, map_ofNat]
  ring

theorem pointLaplaceRate_norm_sq (z w : ℂ) :
    ‖pointLaplaceRate z w‖ ^ 2 =
      4 * Real.pi ^ 2 * Complex.normSq (z - conj w) := by
  rw [Complex.sq_norm]
  simp only [pointLaplaceRate,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  norm_num
  ring

theorem integrable_pointGaussianFactor {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    Integrable (fun t : ℝ => Complex.exp (-pointLaplaceRate z w * (t : ℂ) ^ 2)) :=
  integrable_cexp_neg_mul_sq (pointLaplaceRate_re_pos hz hw)

theorem integral_pointGaussianFactor_mul {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    (∫ t : ℝ, Complex.exp (-pointLaplaceRate z w * (t : ℂ) ^ 2)) *
      (∫ t : ℝ, Complex.exp (-pointLaplaceRate w z * (t : ℂ) ^ 2)) =
        (Real.pi / ‖pointLaplaceRate z w‖ : ℝ) := by
  have hconj :
      (∫ t : ℝ, Complex.exp (-pointLaplaceRate w z * (t : ℂ) ^ 2)) =
        conj (∫ t : ℝ, Complex.exp (-pointLaplaceRate z w * (t : ℂ) ^ 2)) := by
    rw [← integral_conj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      rw [pointLaplaceRate_conj]
      simp [← Complex.exp_conj]
  rw [hconj, Complex.mul_conj']
  have hnorm := congrArg norm
    (integral_gaussian_sq_complex (pointLaplaceRate_re_pos hz hw))
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at hnorm
  exact_mod_cast hnorm

/-- The threshold point kernel is a product of two ordinary convergent Gaussian integrals.
This is the two-Gamma-integral precursor to the continuous-frequency cone transform. -/
theorem pointKernel_one_half_eq_double_gaussian {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel (1 / 2) z w =
      (Real.sqrt (z.im * w.im) : ℂ) *
        (∫ t : ℝ, Complex.exp (-pointLaplaceRate z w * (t : ℂ) ^ 2)) *
        (∫ t : ℝ, Complex.exp (-pointLaplaceRate w z * (t : ℂ) ^ 2)) := by
  rw [mul_assoc, integral_pointGaussianFactor_mul hz hw]
  have hp := pointParameter_pos hz hw
  have hr := pointLaplaceRate_re_pos hz hw
  have hn : pointLaplaceRate z w ≠ 0 := by
    intro h
    simp [h] at hr
  have hn' : ‖pointLaplaceRate z w‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hp' : Complex.normSq (z - conj w) ≠ 0 := by
    have h := pointLaplaceRate_norm_sq z w
    intro hzero
    rw [hzero, mul_zero] at h
    exact hn' (sq_eq_zero_iff.mp h)
  have hsquare : (1 / 4 * pointParameter z w ^ (-(1 / 2) : ℝ)) ^ 2 =
      (Real.sqrt (z.im * w.im) * (Real.pi / ‖pointLaplaceRate z w‖)) ^ 2 := by
    rw [mul_pow, ← Real.rpow_mul_natCast hp.le]
    norm_num
    rw [Real.rpow_neg_one, mul_pow, Real.sq_sqrt (mul_pos hz hw).le,
      div_pow, pointLaplaceRate_norm_sq,
      pointParameter_eq_normSq_sub_conj hz hw]
    field_simp
    ring
  have heq := (sq_eq_sq₀
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (Real.rpow_nonneg hp.le _))
    (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg Real.pi_pos.le (norm_nonneg _)))).mp hsquare
  rw [pointKernel]
  have hpow : (pointParameter z w : ℂ) ^ (-(1 / 2) : ℂ) =
      ((pointParameter z w ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hp.le]
    norm_num
  rw [hpow]
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using congrArg Complex.ofReal heq

/-- The ordinary `s = 1/2` Gamma factor, with no totalized-integral convergence assumption. -/
def pointThresholdLaplaceFactor (z w : ℂ) (t : ℝ) : ℂ :=
  ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * Complex.exp (-pointLaplaceRate z w * t)

private theorem thresholdFactor_substitution (z w : ℂ) {x : ℝ} (hx : 0 < x) :
    ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) • pointThresholdLaplaceFactor z w (x ^ (2 : ℝ)) =
      (2 : ℂ) * Complex.exp (-pointLaplaceRate z w * (x : ℂ) ^ 2) := by
  have hpow : (x ^ (2 : ℝ)) ^ (-(1 / 2) : ℝ) = x⁻¹ := by
    rw [← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg_one]
  simp only [pointThresholdLaplaceFactor, hpow, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_inv]
  norm_num [Real.rpow_two, Complex.ofReal_pow]
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']

theorem integrableOn_pointThresholdLaplaceFactor {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (pointThresholdLaplaceFactor z w) (Ioi 0) := by
  apply (integrableOn_Ioi_comp_rpow_iff _ (show (2 : ℝ) ≠ 0 by norm_num)).mp
  have hg : IntegrableOn (fun t : ℝ =>
      (2 : ℂ) * Complex.exp (-pointLaplaceRate z w * (t : ℂ) ^ 2)) (Ioi 0) :=
    (integrable_pointGaussianFactor hz hw).integrableOn.const_mul _
  apply hg.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa using (thresholdFactor_substitution z w hx).symm

theorem integral_pointThresholdLaplaceFactor {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    (∫ t : ℝ in Ioi 0, pointThresholdLaplaceFactor z w t) =
      ∫ t : ℝ, Complex.exp (-pointLaplaceRate z w * (t : ℂ) ^ 2) := by
  rw [← integral_comp_rpow_Ioi_of_pos (show (0 : ℝ) < 2 by norm_num)]
  calc
    _ = ∫ t : ℝ in Ioi 0,
        (2 : ℂ) * Complex.exp (-pointLaplaceRate z w * (t : ℂ) ^ 2) :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx => thresholdFactor_substitution z w hx
    _ = _ := by
      rw [integral_const_mul, integral_gaussian_complex_Ioi (pointLaplaceRate_re_pos hz hw),
        integral_gaussian_complex (pointLaplaceRate_re_pos hz hw)]
      ring

/-- The actual threshold point kernel has the two ordinary Gamma–Laplace factors whose
light-cone change of variables gives the `C_(1/2) = 1` Fourier–Laplace density. -/
theorem pointKernel_one_half_eq_double_laplace {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel (1 / 2) z w =
      (Real.sqrt (z.im * w.im) : ℂ) *
        (∫ t : ℝ in Ioi 0, pointThresholdLaplaceFactor z w t) *
        (∫ t : ℝ in Ioi 0, pointThresholdLaplaceFactor w z t) := by
  rw [integral_pointThresholdLaplaceFactor hz hw,
    integral_pointThresholdLaplaceFactor hw hz]
  exact pointKernel_one_half_eq_double_gaussian hz hw

theorem integrableOn_pointThresholdLaplaceProduct {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (fun p : ℝ × ℝ =>
      pointThresholdLaplaceFactor z w p.1 * pointThresholdLaplaceFactor w z p.2)
      (Ioi 0 ×ˢ Ioi 0) := by
  rw [IntegrableOn, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    ← MeasureTheory.Measure.prod_restrict]
  exact (integrableOn_pointThresholdLaplaceFactor hz hw).smul_prod
    (integrableOn_pointThresholdLaplaceFactor hw hz)

theorem pointKernel_one_half_eq_quadrant_laplace {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel (1 / 2) z w = (Real.sqrt (z.im * w.im) : ℂ) *
      ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioi 0,
        pointThresholdLaplaceFactor z w p.1 * pointThresholdLaplaceFactor w z p.2 := by
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod_mul, ← mul_assoc]
  exact pointKernel_one_half_eq_double_laplace hz hw

end GapFamily.Analytic.SpatialPoint
