import GapFamily.Analytic.Foundation.IntervalTrace
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Rectangular point estimate

The mixed field is the derivative in the second
coordinate of the first-coordinate derivative. Ordinary iterated integrals
have the first coordinate outside, so the proof requires no Fubini assumption.
-/

noncomputable section
namespace GapFamily.Analytic.RectangleTrace

open Set MeasureTheory

theorem continuous_integral_right {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ × ℝ → E} (hF : Continuous F) {c d : ℝ} (hcd : c ≤ d) :
    Continuous (fun x : ℝ => ∫ y in c..d, F (x, y)) := by
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun x y => F (x, y)) hF (s := Icc c d) isCompact_Icc
  apply h.congr
  intro x
  rw [intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc]

/-- Rectangle estimate with genuine continuous derivative fields. -/
theorem left_point_sq_le_of_derivative_fields
    (F Fx Fy Fxy : ℝ × ℝ → ℂ)
    (hF : Continuous F) (hFx : Continuous Fx) (hFy : Continuous Fy) (hFxy : Continuous Fxy)
    (hdx : ∀ x y, HasDerivAt (fun t => F (t, y)) (Fx (x, y)) x)
    (hdy : ∀ x y, HasDerivAt (fun t => F (x, t)) (Fy (x, y)) y)
    (hdxy : ∀ x y, HasDerivAt (fun t => Fx (x, t)) (Fxy (x, y)) y)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ‖F (a, c)‖^2 ≤
      (4 / ((b-a)*(d-c))) * (∫ x in a..b, ∫ y in c..d, ‖F (x,y)‖^2) +
      (4*(b-a)/(d-c)) * (∫ x in a..b, ∫ y in c..d, ‖Fx (x,y)‖^2) +
      (4*(d-c)/(b-a)) * (∫ x in a..b, ∫ y in c..d, ‖Fy (x,y)‖^2) +
      (4*(b-a)*(d-c)) * (∫ x in a..b, ∫ y in c..d, ‖Fxy (x,y)‖^2) := by
  have hcF : Continuous (fun x => F (x, c)) := hF.comp (continuous_id.prodMk continuous_const)
  have hcFx : Continuous (fun x => Fx (x, c)) := hFx.comp (continuous_id.prodMk continuous_const)
  have ht := IntervalTrace.left_norm_sq_le hab hcF.continuousOn hcFx.continuousOn
    (fun x _ => hdx x c)
  have hv (x : ℝ) := IntervalTrace.left_norm_sq_le hcd
    (hF.comp (continuous_const.prodMk continuous_id)).continuousOn
    (hFy.comp (continuous_const.prodMk continuous_id)).continuousOn (fun y _ => hdy x y)
  have hvx (x : ℝ) := IntervalTrace.left_norm_sq_le hcd
    (hFx.comp (continuous_const.prodMk continuous_id)).continuousOn
    (hFxy.comp (continuous_const.prodMk continuous_id)).continuousOn (fun y _ => hdxy x y)
  have hI := continuous_integral_right (hF.norm.pow 2) hcd.le
  have hIx := continuous_integral_right (hFx.norm.pow 2) hcd.le
  have hIy := continuous_integral_right (hFy.norm.pow 2) hcd.le
  have hIxy := continuous_integral_right (hFxy.norm.pow 2) hcd.le
  simp only [Pi.pow_apply] at hI hIx hIy hIxy
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab.le
    ((hcF.norm.pow 2).intervalIntegrable a b)
    (((hI.const_mul (2/(d-c))).add (hIy.const_mul (2*(d-c)))).intervalIntegrable a b)
    (fun x _ => hv x)
  have hmx := intervalIntegral.integral_mono_on (μ := volume) hab.le
    ((hcFx.norm.pow 2).intervalIntegrable a b)
    (((hIx.const_mul (2/(d-c))).add (hIxy.const_mul (2*(d-c)))).intervalIntegrable a b)
    (fun x _ => hvx x)
  simp only [Pi.add_apply, Pi.pow_apply] at hm hmx
  rw [intervalIntegral.integral_add (μ := volume)
      ((hI.const_mul (2/(d-c))).intervalIntegrable a b)
      ((hIy.const_mul (2*(d-c))).intervalIntegrable a b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
  rw [intervalIntegral.integral_add (μ := volume)
      ((hIx.const_mul (2/(d-c))).intervalIntegrable a b)
      ((hIxy.const_mul (2*(d-c))).intervalIntegrable a b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmx
  calc
    ‖F (a,c)‖^2 ≤ (2/(b-a)) * (∫ x in a..b, ‖F (x,c)‖^2) +
        (2*(b-a)) * (∫ x in a..b, ‖Fx (x,c)‖^2) := ht
    _ ≤ (2/(b-a)) * ((2/(d-c)) * (∫ x in a..b, ∫ y in c..d, ‖F (x,y)‖^2) +
          (2*(d-c)) * (∫ x in a..b, ∫ y in c..d, ‖Fy (x,y)‖^2)) +
        (2*(b-a)) * ((2/(d-c)) * (∫ x in a..b, ∫ y in c..d, ‖Fx (x,y)‖^2) +
          (2*(d-c)) * (∫ x in a..b, ∫ y in c..d, ‖Fxy (x,y)‖^2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
        (mul_le_mul_of_nonneg_left hmx (by linarith))
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Actual first and second coordinate derivatives. -/
def dx (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ F p (1, 0)
def dy (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ F p (0, 1)
def dxy (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ (dx F) p (0, 1)

/-- Point evaluation of an actual `C²` function on a nondegenerate rectangle
is bounded by its value, both first derivatives, and one mixed derivative. -/
theorem left_point_sq_le (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ 2 F)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ‖F (a, c)‖^2 ≤
      (4 / ((b-a)*(d-c))) * (∫ x in a..b, ∫ y in c..d, ‖F (x,y)‖^2) +
      (4*(b-a)/(d-c)) * (∫ x in a..b, ∫ y in c..d, ‖dx F (x,y)‖^2) +
      (4*(d-c)/(b-a)) * (∫ x in a..b, ∫ y in c..d, ‖dy F (x,y)‖^2) +
      (4*(b-a)*(d-c)) * (∫ x in a..b, ∫ y in c..d, ‖dxy F (x,y)‖^2) := by
  have hdx : ContDiff ℝ 1 (dx F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hdy : Continuous (dy F) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdxy : Continuous (dxy F) :=
    (hdx.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply left_point_sq_le_of_derivative_fields F (dx F) (dy F) (dxy F)
    hF.continuous hdx.continuous hdy hdxy ?_ ?_ ?_ hab hcd
  · intro x y
    have hl : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
    exact ((hF.differentiable (by norm_num) (x,y)).hasFDerivAt.comp_hasDerivAt x hl)
  · intro x y
    have hl : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
      (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
    exact ((hF.differentiable (by norm_num) (x,y)).hasFDerivAt.comp_hasDerivAt y hl)
  · intro x y
    have hl : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
      (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
    exact ((hdx.differentiable (by norm_num) (x,y)).hasFDerivAt.comp_hasDerivAt y hl)

end GapFamily.Analytic.RectangleTrace
