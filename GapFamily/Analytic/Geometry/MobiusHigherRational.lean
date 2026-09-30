import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.Basic

noncomputable section

namespace GapFamily.Analytic.LaplacianCovariance

theorem iteratedDeriv_inv_affine (n : ℕ) (c d z : ℂ) :
    iteratedDeriv n (fun w : ℂ => (c * w + d)⁻¹) z =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * c ^ n / (c * z + d) ^ (n + 1) := by
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv_linear]
  simp only
  rw [show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem deriv_inv_affine (c d : ℂ) :
    deriv (fun w : ℂ => (c * w + d)⁻¹) =
      fun w => -c * (1 / (c * w + d) ^ 2) := by
  ext z
  simpa [iteratedDeriv_one, div_eq_mul_inv] using iteratedDeriv_inv_affine 1 c d z

/-- The exact inverse-square affine derivative formula. The constant case is
included; at every nonzero denominator these are the genuine complex derivatives. -/
theorem iteratedDeriv_invSq_affine (n : ℕ) (c d z : ℂ) :
    iteratedDeriv n (fun w : ℂ => 1 / (c * w + d) ^ 2) z =
      (-1 : ℂ) ^ n * ((n + 1).factorial : ℂ) * c ^ n / (c * z + d) ^ (n + 2) := by
  by_cases hc : c = 0
  · subst c
    cases n <;> simp [iteratedDeriv_const]
  · apply mul_left_cancel₀ (neg_ne_zero.mpr hc)
    have h := iteratedDeriv_inv_affine (n + 1) c d z
    rw [iteratedDeriv_succ', deriv_inv_affine, iteratedDeriv_const_mul_field] at h
    rw [h]
    rw [pow_succ (-1 : ℂ) n, pow_succ c n]
    ring

theorem norm_iteratedDeriv_invSq_affine (n : ℕ) (c d z : ℂ) :
    ‖iteratedDeriv n (fun w : ℂ => 1 / (c * w + d) ^ 2) z‖ =
      ((n + 1).factorial : ℝ) * ‖c‖ ^ n / ‖c * z + d‖ ^ (n + 2) := by
  rw [iteratedDeriv_invSq_affine]
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]

end GapFamily.Analytic.LaplacianCovariance
