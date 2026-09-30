import GapFamily.Analytic.Transform.CosRootHalfProfile

/-! Concrete uniform bound for the regular half-line cosRoot profile. -/
noncomputable section
namespace GapFamily.Analytic.CosRootLaplace
open Set MeasureTheory Real

/-- Positive half-line subtraction retains a square-root factor at the origin. -/
theorem norm_regularHalfProfile_le {a : ℝ} (ha : 0 < a) (A : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖regularHalfProfile a A x‖ ≤ (‖A‖ / 2 * Real.exp (‖A‖ / (2 * a))) *
      (Real.sqrt x * Real.exp (-(a / 2) * x)) := by
  have hp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  have hpow : x ^ (-1 / 2 : ℝ) * x = Real.sqrt x := by
    rw [← Real.rpow_add_one hx.ne', Real.sqrt_eq_rpow]
    norm_num
  have hc : ‖cosRoot (A * (x : ℂ)) - 1‖ ≤ ‖A‖ * x / 2 *
      Real.exp (Real.sqrt (‖A‖ * x)) := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] using
      norm_cosRoot_sub_one_le_exp_sqrt (A * (x : ℂ))
  have he : regularHalfProfile a A x = ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      Complex.exp (-(a : ℂ) * (x : ℂ)) * (cosRoot (A * (x : ℂ)) - 1) := by
    simp only [regularHalfProfile, halfProfile, ite_eq_left hx, zero_mul, cosRoot_zero]
    ring
  rw [he, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp,
    Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  calc
    _ ≤ (x ^ (-1 / 2 : ℝ) * Real.exp (-a * x)) *
        (‖A‖ * x / 2 * Real.exp (Real.sqrt (‖A‖ * x))) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (‖A‖ / 2) * Real.sqrt x *
        (Real.exp (-a * x) * Real.exp (Real.sqrt (‖A‖ * x))) := by
      rw [← hpow]; ring
    _ ≤ (‖A‖ / 2) * Real.sqrt x *
        (Real.exp (‖A‖ / (2 * a)) * Real.exp (-(a / 2) * x)) :=
      mul_le_mul_of_nonneg_left (exp_halfProfile_envelope ha A hx.le) (by positivity)
    _ = _ := by ring

private theorem sqrt_mul_exp_neg_le {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    Real.sqrt x * Real.exp (-b * x) ≤ 1 + 1 / b := by
  have hs : Real.sqrt x ≤ 1 + x := by
    nlinarith [Real.sq_sqrt hx, sq_nonneg (Real.sqrt x - 1)]
  have he : Real.exp (-b * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hm : b * x * Real.exp (-b * x) ≤ 1 := by
    have h := Real.mul_exp_neg_le_exp_neg_one (b * x)
    have hh : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    simpa only [neg_mul] using h.trans hh
  have hxe : x * Real.exp (-b * x) ≤ 1 / b := by
    apply (le_div_iff₀ hb).mpr
    nlinarith
  calc
    _ ≤ (1 + x) * Real.exp (-b * x) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = Real.exp (-b * x) + x * Real.exp (-b * x) := by ring
    _ ≤ _ := add_le_add he hxe

/-- An actual finite bound, uniform over the whole real line. -/
theorem norm_regularHalfProfile_uniform {a : ℝ} (ha : 0 < a) (A : ℂ) (x : ℝ) :
    ‖regularHalfProfile a A x‖ ≤
      (‖A‖ / 2 * Real.exp (‖A‖ / (2 * a))) * (1 + 2 / a) := by
  by_cases hx : 0 < x
  · apply (norm_regularHalfProfile_le ha A hx).trans
    have h := sqrt_mul_exp_neg_le (by linarith : 0 < a / 2) hx.le
    have he : 1 / (a / 2) = 2 / a := by ring
    rw [he] at h
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · simp only [regularHalfProfile, halfProfile, ite_eq_right hx, sub_self, norm_zero]
    positivity

/-- Boundedness is proved from the concrete source profile. -/
theorem bddAbove_regularHalfProfile {a : ℝ} (ha : 0 < a) (A : ℂ) :
    BddAbove (Set.range fun x : ℝ => ‖regularHalfProfile a A x‖) := by
  refine ⟨(‖A‖ / 2 * Real.exp (‖A‖ / (2 * a))) * (1 + 2 / a), ?_⟩
  rintro _ ⟨x, rfl⟩
  exact norm_regularHalfProfile_uniform ha A x

end GapFamily.Analytic.CosRootLaplace
