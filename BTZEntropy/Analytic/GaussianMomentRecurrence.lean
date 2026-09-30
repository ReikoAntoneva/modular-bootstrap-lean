import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian moment recurrence

The moments used in the saddle expansion are genuine Lebesgue integrals.
Their recurrence follows from integration by parts on the whole real line.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- Unnormalized real moment with quadratic coefficient `h / 2`. -/
def gaussianRawMoment (h : ℝ) (n : ℕ) : ℝ :=
  ∫ t : ℝ, t ^ n * Real.exp (-h * t ^ 2 / 2)

theorem integrable_gaussianRawMoment {h : ℝ} (hh : 0 < h) (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n * Real.exp (-h * t ^ 2 / 2)) := by
  convert integrable_rpow_mul_exp_neg_mul_sq (div_pos hh (by norm_num : (0 : ℝ) < 2))
    (show (-1 : ℝ) < (n : ℝ) by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) using 1
  ext t
  rw [Real.rpow_natCast]
  congr 2
  ring

theorem gaussianRawMoment_zero (h : ℝ) :
    gaussianRawMoment h 0 = Real.sqrt (2 * Real.pi / h) := by
  unfold gaussianRawMoment
  simp only [pow_zero, one_mul]
  have he : (fun t : ℝ => Real.exp (-h * t ^ 2 / 2)) =
      fun t => Real.exp (-(h / 2) * t ^ 2) := by
    funext t
    congr 1
    ring
  rw [he, integral_gaussian]
  congr 1
  ring

/-- Whole-line integration by parts gives the two-step moment recurrence. -/
theorem gaussianRawMoment_add_two {h : ℝ} (hh : 0 < h) (n : ℕ) :
    gaussianRawMoment h (n + 2) = ((n + 1 : ℕ) : ℝ) / h * gaussianRawMoment h n := by
  have hu (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ (n + 1))
      (((n + 1 : ℕ) : ℝ) * t ^ n) t := by
    simpa only [Pi.pow_def, id_eq, Nat.add_sub_cancel, mul_one] using
      (hasDerivAt_id t).pow (n + 1)
  have hv (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-h * t ^ 2 / 2))
      ((-h) * t * Real.exp (-h * t ^ 2 / 2)) t := by
    convert ((((hasDerivAt_id t).pow 2).const_mul (-h)).div_const 2).exp using 1 <;>
      simp only [Pi.pow_apply, id_eq]
    ring
  have hi₁ : Integrable (fun t : ℝ => t ^ (n + 1) *
      ((-h) * t * Real.exp (-h * t ^ 2 / 2))) := by
    convert (integrable_gaussianRawMoment hh (n + 2)).const_mul (-h) using 1
    ext t
    simp only [pow_succ]
    ring
  have hi₂ : Integrable (fun t : ℝ =>
      (((n + 1 : ℕ) : ℝ) * t ^ n) * Real.exp (-h * t ^ 2 / 2)) := by
    convert (integrable_gaussianRawMoment hh n).const_mul ((n + 1 : ℕ) : ℝ) using 1
    ext t
    ring
  have hr := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t : ℝ => t ^ (n + 1))
    (v := fun t : ℝ => Real.exp (-h * t ^ 2 / 2))
    (u' := fun t : ℝ => ((n + 1 : ℕ) : ℝ) * t ^ n)
    (v' := fun t : ℝ => (-h) * t * Real.exp (-h * t ^ 2 / 2))
    (fun t _ => hu t) (fun t _ => hv t) hi₁ hi₂
    (integrable_gaussianRawMoment hh (n + 1))
  have he₁ : (fun t : ℝ => t ^ (n + 1) *
      ((-h) * t * Real.exp (-h * t ^ 2 / 2))) =
      fun t => (-h) * (t ^ (n + 2) * Real.exp (-h * t ^ 2 / 2)) := by
    funext t
    simp only [pow_succ]
    ring
  have he₂ : (fun t : ℝ =>
      (((n + 1 : ℕ) : ℝ) * t ^ n) * Real.exp (-h * t ^ 2 / 2)) =
      fun t => ((n + 1 : ℕ) : ℝ) * (t ^ n * Real.exp (-h * t ^ 2 / 2)) := by
    funext t
    ring
  rw [he₁, he₂, integral_const_mul, integral_const_mul] at hr
  change -h * gaussianRawMoment h (n + 2) =
    -(((n + 1 : ℕ) : ℝ) * gaussianRawMoment h n) at hr
  apply (mul_left_cancel₀ (ne_of_gt hh))
  field_simp
  nlinarith [hr]

/-- Reflection symmetry makes every odd moment vanish. -/
theorem gaussianRawMoment_odd (h : ℝ) (n : ℕ) :
    gaussianRawMoment h (2 * n + 1) = 0 := by
  have he := integral_neg_eq_self
    (fun t : ℝ => t ^ (2 * n + 1) * Real.exp (-h * t ^ 2 / 2)) volume
  have ho : (fun t : ℝ => (-t) ^ (2 * n + 1) * Real.exp (-h * (-t) ^ 2 / 2)) =
      fun t => -(t ^ (2 * n + 1) * Real.exp (-h * t ^ 2 / 2)) := by
    funext t
    simp [pow_add, pow_mul]
  rw [ho, integral_neg] at he
  change -gaussianRawMoment h (2 * n + 1) = gaussianRawMoment h (2 * n + 1) at he
  linarith

theorem gaussianRawMoment_one (h : ℝ) : gaussianRawMoment h 1 = 0 := by
  simpa using gaussianRawMoment_odd h 0

end BTZEntropy
