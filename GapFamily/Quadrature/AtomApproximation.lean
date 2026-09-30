import GapFamily.Quadrature.MomentCurve
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Continuous density approximation of an atom

A normalized smooth bump supported strictly inside the interval approximates
all the finitely many moment coordinates of any interior point.
-/

open Set MeasureTheory Metric
open scoped Interval

namespace GapFamily.Quadrature

/-- An interior atom has arbitrarily close moments represented by a globally
continuous, nonnegative probability density on the same interval. -/
theorem exists_continuous_density_moment_approximation (k : ℕ) {a b x ε : ℝ}
    (hx : x ∈ Ioo a b) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ t, 0 ≤ f t) ∧
      (∫ t in a..b, f t) = 1 ∧
      ‖(fun i : Fin k => ∫ t in a..b, t ^ (i.val + 1) * f t) -
        momentCurve k x‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp
    (continuous_momentCurve k).continuousAt (ε / 2) (half_pos hε)
  let r := min δ (min (x - a) (b - x))
  have hr : 0 < r := lt_min hδ (lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))
  let φ : ContDiffBump x := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let f : ℝ → ℝ := φ.normed volume
  have hf_cont : Continuous f := φ.continuous_normed
  have hf_nonneg : ∀ t, 0 ≤ f t := φ.nonneg_normed
  have hf_int : Integrable f := φ.integrable_normed
  have hf_mass : (∫ t, f t) = 1 := φ.integral_normed
  have hnear {t : ℝ} (ht : f t ≠ 0) : dist t x < r := by
    have hmem : t ∈ Function.support (φ.normed volume) := ht
    rwa [φ.support_normed_eq] at hmem
  have hsupp : Function.support f ⊆ Ioc a b := by
    intro t ht
    have ht' := hnear ht
    rw [Real.dist_eq, abs_lt] at ht'
    have hra : r ≤ x - a := (min_le_right _ _).trans (min_le_left _ _)
    have hrb : r ≤ b - x := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  refine ⟨f, hf_cont, hf_nonneg, ?_, ?_⟩
  · rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp, hf_mass]
  · have hcoord (i : Fin k) :
        ‖(∫ t in a..b, t ^ (i.val + 1) * f t) - x ^ (i.val + 1)‖ ≤ ε / 2 := by
      have hi : Integrable (fun t => t ^ (i.val + 1) * f t) :=
        ((continuous_id.pow _).mul hf_cont).integrable_of_hasCompactSupport
          (φ.hasCompactSupport_normed.mul_left)
      have hc : Integrable (fun t => x ^ (i.val + 1) * f t) :=
        hf_int.const_mul _
      have heq : (∫ t in a..b, t ^ (i.val + 1) * f t) - x ^ (i.val + 1) =
          ∫ t, (t ^ (i.val + 1) - x ^ (i.val + 1)) * f t := by
        rw [intervalIntegral.integral_eq_integral_of_support_subset]
        · simp_rw [sub_mul]
          rw [integral_sub hi hc, integral_const_mul, hf_mass, mul_one]
        · exact (Function.support_mul_subset_right _ _).trans hsupp
      rw [heq]
      calc
        ‖∫ t, (t ^ (i.val + 1) - x ^ (i.val + 1)) * f t‖ ≤
            ∫ t, (ε / 2) * f t := norm_integral_le_of_norm_le (hf_int.const_mul _)
              (Filter.Eventually.of_forall fun t => ?_)
        _ = ε / 2 := by rw [integral_const_mul, hf_mass, mul_one]
      by_cases ht : f t = 0
      · simp [ht]
      · have hvec := hclose ((hnear ht).trans_le (min_le_left _ _))
        rw [dist_eq_norm] at hvec
        have hpoint : ‖t ^ (i.val + 1) - x ^ (i.val + 1)‖ ≤ ε / 2 :=
          (norm_le_pi_norm (momentCurve k t - momentCurve k x) i).trans hvec.le
        rw [norm_mul, Real.norm_of_nonneg (hf_nonneg t)]
        exact mul_le_mul_of_nonneg_right hpoint (hf_nonneg t)
    exact (pi_norm_le_iff_of_nonneg (half_pos hε).le).mpr hcoord |>.trans_lt (half_lt_self hε)

end GapFamily.Quadrature
