import BTZEntropy.Analytic.SaddleTaylor
import BTZEntropy.Analytic.SaddlePhase

/-!
# Exact finite phase polynomial

The bivariate polynomial used to define the BTZ coefficients is the finite
Taylor polynomial of the reciprocal phase after saddle rescaling.
-/

noncomputable section

open scoped BigOperators

namespace BTZEntropy

/-- Evaluate the displacement variable at `z` and the inverse-square-root charge
variable at `ε`, allowing both variables to be complex. -/
def phaseDeviationValue (x : ℝ) (N : ℕ) (ε z : ℂ) : ℂ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom Complex.ofRealHom z) ε
    (phaseDeviation x N)

theorem phaseDeviationValue_eq_sum (x : ℝ) (N : ℕ) (ε z : ℂ) :
    phaseDeviationValue x N ε z =
      ∑ j ∈ Finset.range N,
        ((-1 : ℂ) ^ (j + 3) * (phaseConstant : ℂ) /
          (saddleBeta x : ℂ) ^ (j + 4)) * z ^ (j + 3) * ε ^ (j + 1) := by
  simp [phaseDeviationValue, phaseDeviation, map_sum,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]

theorem reciprocalTaylor_split (β w : ℂ) (N : ℕ) :
    reciprocalTaylor β w (N + 2) =
      β⁻¹ - w / β ^ 2 + w ^ 2 / β ^ 3 +
        ∑ j ∈ Finset.range N, (-w) ^ (j + 3) / β ^ (j + 4) := by
  induction N with
  | zero =>
      simp [reciprocalTaylor, Finset.sum_range_succ]
      ring
  | succ N ih =>
      rw [show N + 1 + 2 = (N + 2) + 1 by omega, reciprocalTaylor_succ, ih,
        Finset.sum_range_succ]
      ring

/-- The coefficients used in `phaseDeviation` agree exactly with the reciprocal
Taylor coefficients after multiplication by `ε²`. -/
theorem phaseDeviationValue_rescale (x : ℝ) (N : ℕ) (ε z : ℂ) :
    ε ^ 2 * phaseDeviationValue x N ε z =
      (phaseConstant : ℂ) *
        ∑ j ∈ Finset.range N,
          (-(ε * z)) ^ (j + 3) / (saddleBeta x : ℂ) ^ (j + 4) := by
  rw [phaseDeviationValue_eq_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [neg_pow (ε * z)]
  simp only [mul_pow, pow_add, pow_one]
  ring

/-- Exact phase expansion through degree `N + 2` at the specified saddle. -/
theorem complexSaddlePhase_exact_expansion {x : ℝ} (hx : 0 < x)
    (w : ℂ) (hw : (saddleBeta x : ℂ) + w ≠ 0) (N : ℕ) :
    complexSaddlePhase x ((saddleBeta x : ℂ) + w) -
        (saddlePhase x (saddleBeta x) : ℂ) =
      (saddleHessian x : ℂ) / 2 * w ^ 2 +
        (phaseConstant : ℂ) *
          (∑ j ∈ Finset.range N, (-w) ^ (j + 3) / (saddleBeta x : ℂ) ^ (j + 4)) +
        (phaseConstant : ℂ) * reciprocalRemainder (saddleBeta x) w (N + 2) := by
  have hβ : (saddleBeta x : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (saddleBeta_pos hx)
  have hs : (x : ℂ) * (saddleBeta x : ℂ) ^ 2 = (phaseConstant : ℂ) := by
    exact_mod_cast saddleBeta_equation hx
  have hxeq : (x : ℂ) = (phaseConstant : ℂ) / (saddleBeta x : ℂ) ^ 2 :=
    (eq_div_iff (pow_ne_zero _ hβ)).2 hs
  unfold complexSaddlePhase
  rw [saddlePhase_eq_taylor_add_remainder _ _ _ _ hβ hw (N + 2),
    reciprocalTaylor_split]
  simp only [saddlePhase, saddleHessian, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [hxeq]
  field_simp
  ring

/-- The exact scaled phase uses precisely the bivariate polynomial defining the
formal BTZ coefficient algorithm, with an explicit rational remainder. -/
theorem complexSaddlePhase_exact_scaled {x : ℝ} (hx : 0 < x)
    (ε z : ℂ) (hw : (saddleBeta x : ℂ) + ε * z ≠ 0) (N : ℕ) :
    complexSaddlePhase x ((saddleBeta x : ℂ) + ε * z) -
        (saddlePhase x (saddleBeta x) : ℂ) =
      ε ^ 2 * ((saddleHessian x : ℂ) / 2 * z ^ 2 + phaseDeviationValue x N ε z) +
        (phaseConstant : ℂ) * reciprocalRemainder (saddleBeta x) (ε * z) (N + 2) := by
  rw [complexSaddlePhase_exact_expansion hx _ hw N, mul_add,
    phaseDeviationValue_rescale]
  ring

/-- Division by `ε²` is the normalization `c = ε⁻²` used at the saddle. -/
theorem complexSaddlePhase_exact_normalized {x : ℝ} (hx : 0 < x)
    (ε z : ℂ) (hε : ε ≠ 0) (hw : (saddleBeta x : ℂ) + ε * z ≠ 0) (N : ℕ) :
    (complexSaddlePhase x ((saddleBeta x : ℂ) + ε * z) -
        (saddlePhase x (saddleBeta x) : ℂ)) / ε ^ 2 =
      (saddleHessian x : ℂ) / 2 * z ^ 2 + phaseDeviationValue x N ε z +
        (phaseConstant : ℂ) * reciprocalRemainder (saddleBeta x) (ε * z) (N + 2) / ε ^ 2 := by
  rw [complexSaddlePhase_exact_scaled hx _ _ hw N, add_div]
  rw [mul_div_cancel_left₀ _ (pow_ne_zero _ hε)]

/-- The normalized phase error is explicitly of order `‖ε‖^(N+1)`. -/
theorem normalizedPhaseRemainder_norm_le {x : ℝ} (hx : 0 < x)
    (ε z : ℂ) (hε : ε ≠ 0) (hw : ‖ε * z‖ ≤ saddleBeta x / 2) (N : ℕ) :
    ‖(phaseConstant : ℂ) * reciprocalRemainder (saddleBeta x) (ε * z) (N + 2) /
        ε ^ 2‖ ≤
      2 * phaseConstant * ‖ε‖ ^ (N + 1) * ‖z‖ ^ (N + 3) /
        saddleBeta x ^ (N + 4) := by
  have he : ‖ε‖ ≠ 0 := norm_ne_zero_iff.mpr hε
  have hb : saddleBeta x ≠ 0 := ne_of_gt (saddleBeta_pos hx)
  have hbound := phaseRemainder_norm_le (phaseConstant : ℂ) (saddleBeta_pos hx) hw (N + 2)
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos phaseConstant_pos] at hbound
  rw [norm_div, norm_pow]
  calc
    ‖(phaseConstant : ℂ) * reciprocalRemainder (saddleBeta x) (ε * z) (N + 2)‖ /
        ‖ε‖ ^ 2 ≤
      (2 * phaseConstant * ‖ε * z‖ ^ (N + 3) / saddleBeta x ^ (N + 4)) /
        ‖ε‖ ^ 2 := by
          exact div_le_div_of_nonneg_right hbound (sq_nonneg _)
    _ = _ := by
      rw [norm_mul, mul_pow]
      have hp : ‖ε‖ ^ (N + 3) = ‖ε‖ ^ (N + 1) * ‖ε‖ ^ 2 := by
        rw [← pow_add]
      rw [hp]
      field_simp

end BTZEntropy
