import BTZEntropy.Analytic.GaussianMomentRecurrence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Gaussian control of the moving saddle cutoff

Moment bounds convert the complement of `|ε t| < R` into any prescribed
power of `|ε|`. Every polynomially weighted Gaussian has all the required
moments, so replacing truncated Gaussian coefficient integrals by whole-line
integrals loses no finite asymptotic order.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BTZEntropy

theorem integrable_abs_pow_gaussian {h : ℝ} (hh : 0 < h) (n : ℕ) :
    Integrable (fun t : ℝ => |t| ^ n * Real.exp (-h * t ^ 2 / 2)) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)] using
    (integrable_gaussianRawMoment hh n).norm

theorem integrable_one_add_abs_pow_gaussian {h : ℝ} (hh : 0 < h) (n : ℕ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ n * Real.exp (-h * t ^ 2 / 2)) := by
  simp only [add_pow, one_pow, one_mul, Finset.sum_mul]
  apply integrable_finsetSum
  intro j hj
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (integrable_abs_pow_gaussian hh (n - j)).const_mul (n.choose j : ℝ)

theorem integral_norm_outside_scaled_le_moment {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {R ε : ℝ} (hR : 0 < R) (hf : Integrable f)
    (q : ℕ) (hm : Integrable (fun t : ℝ => |t| ^ q * ‖f t‖)) :
    (∫ t in {t : ℝ | R ≤ |ε * t|}, ‖f t‖) ≤
      |ε| ^ q / R ^ q * ∫ t : ℝ, |t| ^ q * ‖f t‖ := by
  have hp (t : ℝ) (ht : R ≤ |ε * t|) :
      ‖f t‖ ≤ |ε| ^ q / R ^ q * (|t| ^ q * ‖f t‖) := by
    have hpow : R ^ q ≤ |ε| ^ q * |t| ^ q := by
      simpa [abs_mul, mul_pow] using pow_le_pow_left₀ (le_of_lt hR) ht q
    have hm := mul_le_mul_of_nonneg_right hpow (norm_nonneg (f t))
    apply (mul_le_mul_iff_right₀ (pow_pos hR q)).mp
    field_simp
    nlinarith
  calc
    (∫ t in {t : ℝ | R ≤ |ε * t|}, ‖f t‖) ≤
        ∫ t in {t : ℝ | R ≤ |ε * t|}, |ε| ^ q / R ^ q * (|t| ^ q * ‖f t‖) := by
      apply integral_mono_ae hf.norm.integrableOn (hm.const_mul _).integrableOn
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_const
        ((continuous_const.mul continuous_id).abs.measurable))] with t ht
      exact hp t ht
    _ = |ε| ^ q / R ^ q * ∫ t in {t : ℝ | R ≤ |ε * t|}, |t| ^ q * ‖f t‖ :=
      integral_const_mul _ _
    _ ≤ |ε| ^ q / R ^ q * ∫ t : ℝ, |t| ^ q * ‖f t‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_le_integral hm (Filter.Eventually.of_forall (fun t => by positivity))

theorem norm_integral_outside_scaled_le_moment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {R ε : ℝ} (hR : 0 < R) (hf : Integrable f)
    (q : ℕ) (hm : Integrable (fun t : ℝ => |t| ^ q * ‖f t‖)) :
    ‖∫ t in {t : ℝ | R ≤ |ε * t|}, f t‖ ≤
      |ε| ^ q / R ^ q * ∫ t : ℝ, |t| ^ q * ‖f t‖ := by
  exact (norm_integral_le_integral_norm _).trans
    (integral_norm_outside_scaled_le_moment hR hf q hm)

/-- Every polynomial Gaussian tail admits every requested inverse-scale power. -/
theorem integral_abs_pow_gaussian_outside_scaled_le {h R ε : ℝ}
    (hh : 0 < h) (hR : 0 < R) (n q : ℕ) :
    (∫ t in {t : ℝ | R ≤ |ε * t|}, |t| ^ n * Real.exp (-h * t ^ 2 / 2)) ≤
      |ε| ^ q / R ^ q * ∫ t : ℝ, |t| ^ (q + n) * Real.exp (-h * t ^ 2 / 2) := by
  have hn : ∀ t : ℝ, ‖|t| ^ n * Real.exp (-h * t ^ 2 / 2)‖ =
      |t| ^ n * Real.exp (-h * t ^ 2 / 2) := by
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hm : Integrable (fun t : ℝ => |t| ^ q *
      ‖|t| ^ n * Real.exp (-h * t ^ 2 / 2)‖) := by
    simpa only [hn, pow_add, mul_assoc] using integrable_abs_pow_gaussian hh (q + n)
  simpa only [hn, pow_add, mul_assoc] using
    integral_norm_outside_scaled_le_moment hR (integrable_abs_pow_gaussian hh n) q hm

end BTZEntropy
