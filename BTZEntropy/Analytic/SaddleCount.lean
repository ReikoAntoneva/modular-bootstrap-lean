import BTZEntropy.Analytic.ContourAmplitude
import BTZEntropy.Analytic.SaddleCauchy
import BTZEntropy.Analytic.Prefactor
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The actual BTZ inverse contour and its saddle scale

The reference observable is the convergent inverse Laplace integral on the
vertical line through the positive saddle. Its normalized version extracts
the exact leading exponential and Gaussian scale.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- The absolutely convergent normalized inverse contour, before the factor `2π`. -/
def normalizedBTZContour (φ : SmoothKernel) (x c : ℝ) : ℂ :=
  ∫ t : ℝ, complexAmplitude φ (saddleContour (saddleBeta x) t) *
    normalizedSaddleExponential x c t

/-- The BTZ smoothed count as the real part of its inverse Laplace contour. -/
def btzCount (φ : SmoothKernel) (x c : ℝ) : ℝ :=
  Real.exp (leadingAction x c) / (2 * Real.pi) * (normalizedBTZContour φ x c).re

/-- The same normalized contour in the Gaussian coordinate. -/
def rescaledBTZContour (φ : SmoothKernel) (x ε : ℝ) : ℂ :=
  ∫ t : ℝ, rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ)

/-- The leading Gaussian integral before dividing the inverse contour by `2π`. -/
def gaussianCountNormalization (φ : SmoothKernel) (x : ℝ) : ℝ :=
  2 * Real.pi * saddlePrefactor φ x

theorem gaussianCountNormalization_pos (φ : SmoothKernel) {x : ℝ} (hx : 0 < x) :
    0 < gaussianCountNormalization φ x :=
  mul_pos (mul_pos (by norm_num) Real.pi_pos) (saddlePrefactor_pos φ hx)

theorem gaussianCountNormalization_eq (φ : SmoothKernel) {x : ℝ} (hx : 0 < x) :
    gaussianCountNormalization φ x =
      Real.sqrt (2 * Real.pi / saddleHessian x) * amplitude φ (saddleBeta x) := by
  have hh := saddleHessian_pos hx
  have hprod : Real.sqrt (2 * Real.pi / saddleHessian x) *
      Real.sqrt (2 * Real.pi * saddleHessian x) = 2 * Real.pi := by
    rw [← Real.sqrt_mul (by positivity)]
    have heq : (2 * Real.pi / saddleHessian x) * (2 * Real.pi * saddleHessian x) =
        (2 * Real.pi) ^ 2 := by field_simp
    rw [heq, Real.sqrt_sq (by positivity)]
  unfold gaussianCountNormalization saddlePrefactor
  have hne : Real.sqrt (2 * Real.pi * saddleHessian x) ≠ 0 := by positivity
  calc
    _ = (Real.sqrt (2 * Real.pi / saddleHessian x) *
          Real.sqrt (2 * Real.pi * saddleHessian x)) *
        (amplitude φ (saddleBeta x) / Real.sqrt (2 * Real.pi * saddleHessian x)) := by
      rw [hprod]
    _ = _ := by field_simp

theorem integrable_normalizedBTZContour (φ : SmoothKernel) {x c : ℝ}
    (hx : 0 < x) (hc : 0 ≤ c) :
    Integrable (fun t : ℝ => complexAmplitude φ (saddleContour (saddleBeta x) t) *
      normalizedSaddleExponential x c t) := by
  exact integrable_mul_normalizedSaddleExponential hx hc
    (integrable_complexAmplitude_contour φ (saddleBeta_pos hx))

/-- The exact saddle equation cancels the linear term without an asymptotic limit. -/
theorem complexSaddlePhase_sub_exact {x : ℝ} (hx : 0 < x)
    (w : ℂ) (hw : (saddleBeta x : ℂ) + w ≠ 0) :
    complexSaddlePhase x ((saddleBeta x : ℂ) + w) -
      (saddlePhase x (saddleBeta x) : ℂ) =
        (phaseConstant : ℂ) * w ^ 2 /
          ((saddleBeta x : ℂ) ^ 2 * ((saddleBeta x : ℂ) + w)) := by
  have hβ : (saddleBeta x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (saddleBeta_pos hx)
  have hs : (x : ℂ) * (saddleBeta x : ℂ) ^ 2 = (phaseConstant : ℂ) := by
    exact_mod_cast saddleBeta_equation hx
  have hxeq : (x : ℂ) = (phaseConstant : ℂ) / (saddleBeta x : ℂ) ^ 2 :=
    (eq_div_iff (pow_ne_zero _ hβ)).2 hs
  simp only [complexSaddlePhase, saddlePhase, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div]
  rw [hxeq]
  field_simp
  ring

theorem rescaledSaddleIntegrand_eq_original (φ : SmoothKernel) {x c ε : ℝ}
    (hx : 0 < x) (hcε : c * ε ^ 2 = 1) (t : ℝ) :
    rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ) =
      complexAmplitude φ (saddleContour (saddleBeta x) (ε * t)) *
        normalizedSaddleExponential x c (ε * t) := by
  have harg : (saddleBeta x : ℂ) + Complex.I * (ε : ℂ) * (t : ℂ) =
      saddleContour (saddleBeta x) (ε * t) := by
    simp only [saddleContour, Complex.ofReal_mul]
    ring
  have hw : (saddleBeta x : ℂ) + Complex.I * (ε : ℂ) * (t : ℂ) ≠ 0 := by
    rw [harg]
    exact saddleContour_ne_zero (ne_of_gt (saddleBeta_pos hx)) _
  have hcεc : (c : ℂ) * (ε : ℂ) ^ 2 = 1 := by exact_mod_cast hcε
  unfold rescaledSaddleIntegrand normalizedSaddleExponential
  rw [← harg]
  congr 2
  rw [complexSaddlePhase_sub_exact hx (Complex.I * (ε : ℂ) * (t : ℂ)) hw]
  simp only [div_eq_mul_inv]
  rw [← mul_assoc (c : ℂ)]
  have heq : (c : ℂ) * ((phaseConstant : ℂ) * (Complex.I * (ε : ℂ) * (t : ℂ)) ^ 2) =
      -(phaseConstant : ℂ) * (t : ℂ) ^ 2 := by
    rw [mul_pow, mul_pow, Complex.I_sq]
    calc
      _ = -(phaseConstant : ℂ) * (t : ℂ) ^ 2 * ((c : ℂ) * (ε : ℂ) ^ 2) := by ring
      _ = _ := by rw [hcεc, mul_one]
  rw [heq]

/-- Real dilation of the convergent contour is exactly the saddle rescaling. -/
theorem normalizedBTZContour_eq_rescaled (φ : SmoothKernel) {x c ε : ℝ}
    (hx : 0 < x) (hε : 0 < ε) (hcε : c * ε ^ 2 = 1) :
    normalizedBTZContour φ x c = (ε : ℂ) * rescaledBTZContour φ x ε := by
  have hf : (fun t : ℝ => rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ)) =
      fun t : ℝ => complexAmplitude φ (saddleContour (saddleBeta x) (ε * t)) *
        normalizedSaddleExponential x c (ε * t) :=
    funext (rescaledSaddleIntegrand_eq_original φ hx hcε)
  let f : ℝ → ℂ := fun t => complexAmplitude φ (saddleContour (saddleBeta x) t) *
    normalizedSaddleExponential x c t
  rw [rescaledBTZContour, hf]
  change normalizedBTZContour φ x c = (ε : ℂ) * ∫ t : ℝ, f (ε * t)
  rw [Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr hε), Complex.real_smul]
  rw [← mul_assoc]
  change normalizedBTZContour φ x c =
    (ε : ℂ) * ((ε⁻¹ : ℝ) : ℂ) * normalizedBTZContour φ x c
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hε), Complex.ofReal_one, one_mul]

theorem normalizedBTZContour_eq_rescaled_sqrt (φ : SmoothKernel) {x c : ℝ}
    (hx : 0 < x) (hc : 0 < c) :
    normalizedBTZContour φ x c = ((Real.sqrt c)⁻¹ : ℂ) *
      rescaledBTZContour φ x (Real.sqrt c)⁻¹ := by
  rw [← Complex.ofReal_inv]
  apply normalizedBTZContour_eq_rescaled φ hx (inv_pos.mpr (Real.sqrt_pos.mpr hc))
  rw [inv_pow, Real.sq_sqrt hc.le, mul_inv_cancel₀ (ne_of_gt hc)]

theorem integrable_rescaledBTZContour (φ : SmoothKernel) {x ε : ℝ}
    (hx : 0 < x) (hε : ε ≠ 0) :
    Integrable (fun t : ℝ => rescaledSaddleIntegrand (complexAmplitude φ)
      (saddleBeta x) t (ε : ℂ)) := by
  have hce : (ε ^ 2)⁻¹ * ε ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero _ hε)
  have hf := (integrable_normalizedBTZContour φ hx (inv_nonneg.mpr (sq_nonneg ε))).comp_mul_left' hε
  exact hf.congr (Filter.Eventually.of_forall (fun t =>
    (rescaledSaddleIntegrand_eq_original φ hx hce t).symm))

/-- The count normalized by the prescribed Gaussian scale is exactly the real
rescaled contour divided by its leading Gaussian integral. -/
theorem btzCount_div_scale (φ : SmoothKernel) {x c : ℝ}
    (hx : 0 < x) (hc : 0 < c) :
    btzCount φ x c / saddleCountScale φ x c =
      (rescaledBTZContour φ x (Real.sqrt c)⁻¹).re / gaussianCountNormalization φ x := by
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hsf : saddlePrefactor φ x ≠ 0 := ne_of_gt (saddlePrefactor_pos φ hx)
  have hsc : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  unfold btzCount saddleCountScale gaussianCountNormalization
  rw [normalizedBTZContour_eq_rescaled_sqrt φ hx hc]
  simp only [Complex.mul_re, Complex.inv_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.normSq_ofReal, Complex.inv_im, neg_zero, zero_div, zero_mul, sub_zero]
  field_simp

end BTZEntropy
