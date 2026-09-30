import GapFamily.Analytic.Poincare.PoincareAnalytic
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
namespace GapFamily.Analytic.PoincareSeedGradient

/-- The literal zero-energy seed in ordinary complex coordinates. -/
def rawSeed (J : ℤ) (s : ℂ) (z : ℂ) : ℂ :=
  (z.im : ℂ) ^ s * Complex.exp
    (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * Complex.I)

theorem rawSeed_eq_complexPointSeed (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    rawSeed J s τ = complexPointSeed 0 J s τ := by
  simp only [rawSeed, complexPointSeed, mul_zero, zero_mul, zero_add]
  rfl

/-- The real spatial derivative, split into its imaginary and real directions. -/
def rawSeedDerivative (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) : ℂ →L[ℝ] ℂ :=
  (s * (τ.im : ℂ) ^ (s - 1) *
    Complex.exp (((2 * Real.pi * (J : ℝ) * τ.re : ℝ) : ℂ) * Complex.I)) •
      (Complex.ofRealCLM.comp Complex.imCLM) +
  ((τ.im : ℂ) ^ s *
    Complex.exp (((2 * Real.pi * (J : ℝ) * τ.re : ℝ) : ℂ) * Complex.I) *
    ((2 * Real.pi * (J : ℝ) : ℝ) : ℂ) * Complex.I) •
      (Complex.ofRealCLM.comp Complex.reCLM)

theorem hasFDerivAt_rawSeed (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    HasFDerivAt (rawSeed J s) (rawSeedDerivative J s τ) (τ : ℂ) := by
  have hpow := (Complex.hasStrictDerivAt_cpow_const (c := s)
    (x := (τ.im : ℂ)) (Or.inl τ.im_pos)).hasDerivAt.comp_hasFDerivAt (τ : ℂ)
      ((Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt)
  have harg := ((Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt (x := (τ : ℂ))).const_mul
    (((2 * Real.pi * (J : ℝ) : ℝ) : ℂ) * Complex.I)
  have hprod := hpow.mul harg.cexp
  convert hprod using 1
  · ext z
    simp only [rawSeed, Pi.mul_apply, ContinuousLinearMap.comp_apply,
      Complex.reCLM_apply, Complex.ofRealCLM_apply,
      Complex.ofReal_mul]
    congr 2
    ring
  · ext v
    simp only [rawSeedDerivative, add_apply,
      smul_apply, ContinuousLinearMap.comp_apply, Function.comp_apply,
      Complex.imCLM_apply, Complex.reCLM_apply, Complex.ofRealCLM_apply,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, smul_eq_mul]
    have he : (((2 : ℝ) * Real.pi * (J : ℝ) : ℝ) : ℂ) * Complex.I * ↑τ.re =
        ↑(2 * Real.pi * (J : ℝ) * τ.re) * Complex.I := by push_cast; ring
    rw [he]
    ring

theorem differentiableAt_rawSeed (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    DifferentiableAt ℝ (rawSeed J s) (τ : ℂ) :=
  (hasFDerivAt_rawSeed J s τ).differentiableAt

theorem fderiv_rawSeed (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    fderiv ℝ (rawSeed J s) (τ : ℂ) = rawSeedDerivative J s τ :=
  (hasFDerivAt_rawSeed J s τ).fderiv

theorem norm_fderiv_rawSeed_le (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) (v : ℂ) :
    ‖fderiv ℝ (rawSeed J s) (τ : ℂ) v‖ ≤
      (‖s‖ / τ.im + 2 * Real.pi * |(J : ℝ)|) * τ.im ^ s.re * ‖v‖ := by
  rw [fderiv_rawSeed]
  simp only [rawSeedDerivative, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    Complex.imCLM_apply, Complex.reCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_cpow_eq_rpow_re_of_pos τ.im_pos, Complex.sub_re, Complex.one_re,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [Real.rpow_sub_one τ.im_pos.ne']
  calc
    _ ≤ (‖s‖ * (τ.im ^ s.re / τ.im)) * ‖v‖ +
        (τ.im ^ s.re * (2 * Real.pi * |(J : ℝ)|)) * ‖v‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm v) (by positivity))
        (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm v) (by positivity))
    _ = _ := by ring

/-- The actual hyperbolic-frame scale is controlled using only the point's
positive height, with no uniform lower-height assumption. -/
theorem frame_norm_fderiv_rawSeed_le (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) (v : ℂ) :
    τ.im * ‖fderiv ℝ (rawSeed J s) (τ : ℂ) v‖ ≤
      (‖s‖ + 2 * Real.pi * |(J : ℝ)| * τ.im) * τ.im ^ s.re * ‖v‖ := by
  calc
    _ ≤ τ.im * ((‖s‖ / τ.im + 2 * Real.pi * |(J : ℝ)|) * τ.im ^ s.re * ‖v‖) :=
      mul_le_mul_of_nonneg_left (norm_fderiv_rawSeed_le J s τ v) τ.im_pos.le
    _ = _ := by field_simp

end GapFamily.Analytic.PoincareSeedGradient
