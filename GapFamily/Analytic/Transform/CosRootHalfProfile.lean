import GapFamily.Analytic.Transform.CosRootSqrtBound
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Convolution

/-! Actual integrable half-line cosRoot profiles and their bounded continuous subtraction. -/
noncomputable section
namespace GapFamily.Analytic.CosRootLaplace
open Set MeasureTheory Real
open scoped Topology

/-- The literal damped half-line profile; its scalar singularity is integrable. -/
def halfProfile (a : ℝ) (A : ℂ) (x : ℝ) : ℂ :=
  if 0 < x then ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
    Complex.exp (-(a : ℂ) * (x : ℂ)) * cosRoot (A * (x : ℂ)) else 0

/-- Removing the constant cosRoot term cancels the half-line origin singularity. -/
def regularHalfProfile (a : ℝ) (A : ℂ) (x : ℝ) : ℂ :=
  halfProfile a A x - halfProfile a 0 x

private theorem sqrt_young {a x N : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hN : 0 ≤ N) :
    Real.sqrt (N * x) ≤ a / 2 * x + N / (2 * a) := by
  have he : N / (2 * a) = (N / a) / 2 := by ring
  rw [he]
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  have hd : a * (N / a) = N := mul_div_cancel₀ _ ha.ne'
  nlinarith [sq_nonneg (a * x - N / a)]

/-- Square-root growth is dominated by a genuine exponential-decay envelope. -/
theorem exp_halfProfile_envelope {a : ℝ} (ha : 0 < a) (A : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-a * x) * Real.exp (Real.sqrt (‖A‖ * x)) ≤
      Real.exp (‖A‖ / (2 * a)) * Real.exp (-(a / 2) * x) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := sqrt_young ha hx (norm_nonneg A)
  linarith

/-- Pointwise ordinary absolute-integrability majorant for every complex coefficient. -/
theorem norm_halfProfile_le {a : ℝ} (ha : 0 < a) (A : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖halfProfile a A x‖ ≤ Real.exp (‖A‖ / (2 * a)) *
      (x ^ (-1 / 2 : ℝ) * Real.exp (-(a / 2) * x)) := by
  have hp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  have hc : ‖cosRoot (A * (x : ℂ))‖ ≤ Real.exp (Real.sqrt (‖A‖ * x)) := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] using
      norm_cosRoot_le_exp_sqrt (A * (x : ℂ))
  simp only [halfProfile, ite_eq_left hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hp, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  calc
    _ ≤ x ^ (-1 / 2 : ℝ) * (Real.exp (-a * x) *
        Real.exp (Real.sqrt (‖A‖ * x))) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc
        (mul_nonneg hp (Real.exp_pos _).le)
    _ ≤ x ^ (-1 / 2 : ℝ) * (Real.exp (‖A‖ / (2 * a)) *
        Real.exp (-(a / 2) * x)) := mul_le_mul_of_nonneg_left
      (exp_halfProfile_envelope ha A hx.le) hp
    _ = _ := by ring

/-- Actual half-profile integrability; no transform or integrability oracle is assumed. -/
theorem integrable_halfProfile {a : ℝ} (ha : 0 < a) (A : ℂ) :
    Integrable (halfProfile a A) volume := by
  have hpow : IntegrableOn (fun x : ℝ => x ^ (-1 / 2 : ℝ) *
      Real.exp (-(a / 2) * x)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (-1 / 2 : ℝ)) (p := 1) (by norm_num) (by norm_num) (by linarith : 0 < a / 2)
  have hc : ContinuousOn (fun x : ℝ => ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      Complex.exp (-(a : ℂ) * (x : ℂ)) * cosRoot (A * (x : ℂ))) (Ioi 0) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact Complex.continuous_ofReal.comp_continuousOn (fun x hx =>
          (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx))).continuousWithinAt)
      · fun_prop
    · exact cosRoot_continuous.comp_continuousOn (by fun_prop)
  have hi : IntegrableOn (fun x : ℝ => ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      Complex.exp (-(a : ℂ) * (x : ℂ)) * cosRoot (A * (x : ℂ))) (Ioi 0) := by
    apply (hpow.const_mul (Real.exp (‖A‖ / (2 * a)))).mono' (hc.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    change 0 < x at hx
    simpa only [halfProfile, ite_eq_left hx] using norm_halfProfile_le ha A hx
  have he : halfProfile a A = (Ioi (0 : ℝ)).indicator (fun x : ℝ =>
      ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * (x : ℂ)) *
        cosRoot (A * (x : ℂ))) := by
    funext x
    rfl
  rw [he]
  exact hi.integrable_indicator measurableSet_Ioi

/-- The actual subtraction is integrable. -/
theorem integrable_regularHalfProfile {a : ℝ} (ha : 0 < a) (A : ℂ) :
    Integrable (regularHalfProfile a A) volume :=
  (integrable_halfProfile ha A).sub (integrable_halfProfile ha 0)

/-- Literal removal of the zero-energy singularity. -/
theorem regularHalfProfile_eq_dslope (a : ℝ) (A : ℂ) (x : ℝ) :
    regularHalfProfile a A x = ((Real.sqrt (max x 0) : ℝ) : ℂ) *
      Complex.exp (-(a : ℂ) * (x : ℂ)) * (A * dslope cosRoot 0 (A * (x : ℂ))) := by
  by_cases hx : 0 < x
  · have hp : x ^ (-1 / 2 : ℝ) * x = Real.sqrt x := by
      rw [← Real.rpow_add_one hx.ne', Real.sqrt_eq_rpow]
      norm_num
    have hpC : ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * (x : ℂ) = (Real.sqrt x : ℂ) := by
      exact_mod_cast hp
    have hd := sub_smul_dslope cosRoot (0 : ℂ) (A * (x : ℂ))
    simp only [sub_zero, smul_eq_mul, cosRoot_zero] at hd
    simp only [regularHalfProfile, halfProfile, ite_eq_left hx, zero_mul, cosRoot_zero,
      mul_one, max_eq_left hx.le]
    calc
      _ = ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * (x : ℂ)) *
          (cosRoot (A * (x : ℂ)) - 1) := by ring
      _ = _ := by rw [← hd, ← hpC]; ring
  · simp [regularHalfProfile, halfProfile, hx, max_eq_right (le_of_not_gt hx)]

/-- The subtraction extends continuously through the origin with value zero. -/
theorem continuous_regularHalfProfile (a : ℝ) (A : ℂ) : Continuous (regularHalfProfile a A) := by
  have hd : Continuous (dslope cosRoot (0 : ℂ)) := by
    apply continuousOn_univ.mp
    exact (continuousOn_dslope (s := univ) (by simp)).mpr
      ⟨cosRoot_continuous.continuousOn, (cosRoot_analyticAt 0).differentiableAt⟩
  simp_rw [show regularHalfProfile a A = fun x => ((Real.sqrt (max x 0) : ℝ) : ℂ) *
      Complex.exp (-(a : ℂ) * (x : ℂ)) * (A * dslope cosRoot 0 (A * (x : ℂ))) from
    funext (regularHalfProfile_eq_dslope a A)]
  apply Continuous.mul (by fun_prop)
  exact continuous_const.mul (hd.comp (by fun_prop))

end GapFamily.Analytic.CosRootLaplace
