import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileCore
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Ordinary integrability of the actual unrolled nonidentity Fourier kernel.
The estimates retain the exact height and denominator normalization.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareFourierUnfold

open Set MeasureTheory

/-- The literal unrolled kernel, with input and output Fourier phases. -/
def fourierKernel (c y : ℝ) (j J : ℤ) (s : ℂ) (t : ℝ) : ℂ :=
  ((y / (c ^ 2 * (t ^ 2 + y ^ 2)) : ℝ) : ℂ) ^ s *
    cuspFourierMode (-J) (t / (c ^ 2 * (t ^ 2 + y ^ 2))) * cuspFourierMode (-j) t

/-- Both literal Fourier factors have unit norm. -/
theorem norm_fourierKernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) (s : ℂ) (t : ℝ) :
    ‖fourierKernel c y j J s t‖ = (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ s.re := by
  simp only [fourierKernel, norm_mul, norm_cuspFourierMode, mul_one]
  exact Complex.norm_cpow_eq_rpow_re_of_pos
    (by positivity : 0 < y / (c ^ 2 * (t ^ 2 + y ^ 2))) s

/-- The actual kernel is continuous at every real unrolled coordinate. -/
theorem continuous_fourierKernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) (s : ℂ) : Continuous (fourierKernel c y j J s) := by
  have hd : Continuous (fun t : ℝ => c ^ 2 * (t ^ 2 + y ^ 2)) := by fun_prop
  have hdn (t : ℝ) : c ^ 2 * (t ^ 2 + y ^ 2) ≠ 0 := by positivity
  have hb : Continuous (fun t : ℝ => y / (c ^ 2 * (t ^ 2 + y ^ 2))) :=
    continuous_const.div hd hdn
  have hp : Continuous (fun t : ℝ => ((y / (c ^ 2 * (t ^ 2 + y ^ 2)) : ℝ) : ℂ) ^ s) :=
    (Complex.continuous_ofReal.comp hb).cpow continuous_const
      (fun t => Or.inl (by change 0 < y / (c ^ 2 * (t ^ 2 + y ^ 2)); positivity))
  exact (hp.mul ((contDiff_cuspFourierMode (-J)).continuous.comp
    (continuous_id.div hd hdn))).mul (contDiff_cuspFourierMode (-j)).continuous

private theorem kernelNorm_factor {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (σ t : ℝ) :
    (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ σ =
      (1 / (c ^ 2 * y)) ^ σ * (1 + (t / y) ^ 2) ^ (-σ) := by
  have hq : t ^ 2 + y ^ 2 ≠ 0 := by positivity
  have he : y / (c ^ 2 * (t ^ 2 + y ^ 2)) =
      (1 / (c ^ 2 * y)) / (1 + (t / y) ^ 2) := by
    field_simp [hc.ne', hy.ne', hq]
    ring
  rw [he, Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
    div_eq_mul_inv]

private theorem integrable_kernelNorm {c y σ : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hσ : 1 / 2 < σ) :
    Integrable (fun t : ℝ => (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ σ) volume := by
  have hstd : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-σ)) volume := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * σ)
      (by simpa using (show (1 : ℝ) < 2 * σ by linarith))
    convert h using 1
    funext t
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  apply ((hstd.comp_div hy.ne').const_mul ((1 / (c ^ 2 * y)) ^ σ)).congr
  filter_upwards with t
  exact (kernelNorm_factor hc hy σ t).symm

/-- Genuine ordinary integrability holds already in the sharp half-plane
Re(s)>1/2, with no assumed kernel-integrability input. -/
theorem integrable_fourierKernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (fourierKernel c y j J s) volume := by
  apply (integrable_kernelNorm hc hy hs).mono'
    (continuous_fourierKernel hc hy j J s).aestronglyMeasurable
  filter_upwards with t
  exact (norm_fourierKernel hc hy j J s t).le

private theorem integral_shifted_unitInterval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (a : ℝ) (k : ℤ) :
    (∫ x in (0 : ℝ)..1, f (x + a + k)) =
      ∫ x in a + k..a + k + 1, f x := by
  have he : (fun x : ℝ => f (x + a + k)) = fun x => f (x + (a + k)) := by
    funext x
    rw [add_assoc]
  rw [he, intervalIntegral.integral_comp_add_right, zero_add]
  congr 1
  ring

/-- A genuinely integrable function unfolds over every real translate of the
ordinary unit-interval partition. -/
theorem hasSum_integral_shifted_unitInterval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f volume) (a : ℝ) :
    HasSum (fun k : ℤ => ∫ x in (0 : ℝ)..1, f (x + a + k)) (∫ t, f t) := by
  simpa only [integral_shifted_unitInterval] using hf.hasSum_intervalIntegral a

/-- The shifted partition has summable ordinary integrated norms. -/
theorem summable_integral_norm_shifted_unitInterval
    {f : ℝ → ℂ} (hf : Integrable f volume) (a : ℝ) :
    Summable (fun k : ℤ => ∫ x in (0 : ℝ)..1, ‖f (x + a + k)‖) :=
  (hasSum_integral_shifted_unitInterval hf.norm a).summable

/-- Actual shifted-interval unfolding of the literal Fourier kernel. -/
theorem hasSum_intervalIntegral_fourierKernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) (a : ℝ) :
    HasSum (fun k : ℤ => ∫ x in (0 : ℝ)..1, fourierKernel c y j J s (x + a + k))
      (∫ t : ℝ, fourierKernel c y j J s t) :=
  hasSum_integral_shifted_unitInterval (integrable_fourierKernel hc hy j J hs) a

/-- Absolute integral summability for the same actual shifted kernel terms. -/
theorem summable_intervalIntegral_norm_fourierKernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) (a : ℝ) :
    Summable (fun k : ℤ => ∫ x in (0 : ℝ)..1, ‖fourierKernel c y j J s (x + a + k)‖) :=
  summable_integral_norm_shifted_unitInterval (integrable_fourierKernel hc hy j J hs) a

end GapFamily.Analytic.PoincareFourierUnfold
