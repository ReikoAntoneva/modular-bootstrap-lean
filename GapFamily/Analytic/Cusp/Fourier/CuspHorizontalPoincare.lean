import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Horizontal Poincaré estimate

The ordinary interval mean satisfies a Poincaré estimate with the square of
the interval length. The proof uses the integral of the derivative to bound
every pairwise difference, followed by the integral Cauchy inequality. In
particular the unit cusp interval has constant one; periodicity is unnecessary.
-/

open Set MeasureTheory

namespace GapFamily.Analytic

/-- Scalar integral Cauchy on an interval, proved by expanding an actual
nonnegative square. Continuity supplies every needed integrability fact. -/
theorem integral_sq_le_length_mul_integral_sq {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, g x)^2 ≤ (b - a) * (∫ x in a..b, (g x)^2) := by
  let m : ℝ := ∫ x in a..b, g x
  let d : ℝ := b - a
  have hd : 0 < d := sub_pos.mpr hab
  have hgi : IntervalIntegrable g volume a b := hg.intervalIntegrable a b
  have hg2i : IntervalIntegrable (fun x => (g x)^2) volume a b :=
    (hg.pow 2).intervalIntegrable a b
  have hpoly : (fun x => (d * g x - m)^2) =
      (fun x => d^2 * (g x)^2 - (2 * d * m) * g x + m^2) := by
    funext x
    ring
  have hvariance : (∫ x in a..b, (d * g x - m)^2) =
      d * (d * (∫ x in a..b, (g x)^2) - m^2) := by
    rw [hpoly,
      intervalIntegral.integral_add
        ((hg2i.const_mul (d^2)).sub (hgi.const_mul (2 * d * m))) intervalIntegrable_const,
      intervalIntegral.integral_sub (hg2i.const_mul (d^2)) (hgi.const_mul (2 * d * m)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    change d^2 * (∫ x in a..b, (g x)^2) - (2 * d * m) * m + d * m^2 =
      d * (d * (∫ x in a..b, (g x)^2) - m^2)
    ring
  have hnonneg : 0 ≤ ∫ x in a..b, (d * g x - m)^2 :=
    intervalIntegral.integral_nonneg_of_forall hab.le (fun _ => sq_nonneg _)
  rw [hvariance] at hnonneg
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hd).mp hnonneg)

/-- Every pairwise displacement is controlled by the derivative integral over
the whole interval. -/
theorem norm_sub_le_deriv_integral_of_mem (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    {a b x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ ≤ ∫ t in a..b, ‖deriv f t‖ := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd : Continuous (fun t => ‖deriv f t‖) := hf.continuous_deriv_one.norm
  have haux : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      ‖f v - f u‖ ≤ ∫ t in a..b, ‖deriv f t‖ := by
    intro u hu v hv huv
    apply (norm_sub_le_integral_of_norm_deriv_le_of_le huv hf.continuous.continuousOn
      hfd.differentiableOn (Filter.Eventually.of_forall fun _ _ => le_rfl)
        (hd.intervalIntegrable u v)).trans
    exact intervalIntegral.integral_mono_interval hu.1 huv hv.2
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hd.intervalIntegrable a b)
  rcases le_total y x with hxy | hyx
  · exact haux y hy x hx hxy
  · rw [norm_sub_rev]
    exact haux x hx y hy hyx

/-- The deviation from the actual interval mean is bounded pointwise by the
integral of the derivative norm. -/
theorem norm_sub_interval_mean_le_deriv_integral (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    ‖f x - (b - a)⁻¹ • (∫ t in a..b, f t)‖ ≤ ∫ t in a..b, ‖deriv f t‖ := by
  have hbound : ∀ t ∈ uIoc a b,
      ‖f x - f t‖ ≤ ∫ s in a..b, ‖deriv f s‖ := by
    intro t ht
    rw [uIoc_of_le hab.le] at ht
    exact norm_sub_le_deriv_integral_of_mem f hf hx ⟨ht.1.le, ht.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.continuous.intervalIntegrable a b),
    intervalIntegral.integral_const, abs_of_pos (sub_pos.mpr hab)] at h
  have heq : (b - a) • (f x - (b - a)⁻¹ • (∫ t in a..b, f t)) =
      (b - a) • f x - ∫ t in a..b, f t := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (sub_pos.mpr hab).ne', one_smul]
  rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] at h
  exact (mul_le_mul_iff_right₀ (sub_pos.mpr hab)).mp (by simpa only [mul_comm] using h)

/-- Poincaré on an arbitrary nondegenerate interval with its normalized
ordinary mean. No periodicity or unproved integrability hypothesis is used. -/
theorem interval_poincare (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, ‖f x - (b - a)⁻¹ • (∫ t in a..b, f t)‖^2) ≤
      (b - a)^2 * (∫ x in a..b, ‖deriv f x‖^2) := by
  let D : ℝ := ∫ t in a..b, ‖deriv f t‖
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg hab.le (fun _ _ => norm_nonneg _)
  have hi : IntervalIntegrable
      (fun x => ‖f x - (b - a)⁻¹ • (∫ t in a..b, f t)‖^2) volume a b :=
    ((hf.continuous.sub continuous_const).norm.pow 2).intervalIntegrable a b
  have hpoint : ∀ x ∈ Icc a b, ‖f x - (b - a)⁻¹ • (∫ t in a..b, f t)‖^2 ≤ D^2 := by
    intro x hx
    exact (sq_le_sq₀ (norm_nonneg _) hD).mpr
      (norm_sub_interval_mean_le_deriv_integral f hf hab hx)
  have hmono := intervalIntegral.integral_mono_on hab.le hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => D^2) volume a b) hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hc := integral_sq_le_length_mul_integral_sq hf.continuous_deriv_one.norm hab
  calc
    (∫ x in a..b, ‖f x - (b - a)⁻¹ • (∫ t in a..b, f t)‖^2) ≤ (b - a) * D^2 := hmono
    _ ≤ (b - a) * ((b - a) * (∫ x in a..b, ‖deriv f x‖^2)) :=
      mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hab.le)
    _ = (b - a)^2 * (∫ x in a..b, ‖deriv f x‖^2) := by ring

/-- Unit-length intervals have ordinary integral equal to normalized mean. -/
theorem unit_interval_poincare (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (a : ℝ) :
    (∫ x in a..a + 1, ‖f x - ∫ t in a..a + 1, f t‖^2) ≤
      ∫ x in a..a + 1, ‖deriv f x‖^2 := by
  simpa using interval_poincare f hf (show a < a + 1 by linarith)

/-- The actual centered horizontal cusp interval. -/
theorem cusp_horizontal_poincare (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), ‖f x - ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), f t‖^2) ≤
      ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), ‖deriv f x‖^2 := by
  simpa only [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] using
    unit_interval_poincare f hf (-1 / 2)

end GapFamily.Analytic
