import BTZEntropy.Analytic.SaddleExpansion

/-!
# Finite exponential of the saddle correction

The finite polynomial in the coefficient algorithm is the Taylor polynomial
of the actual exponential of the exact finite phase deviation. Quantitative
remainders here apply to the rational BTZ phase itself.
-/

noncomputable section

open scoped BigOperators

namespace BTZEntropy

/-- Evaluation of the existing finite exponential in its two complex variables. -/
def phaseExponentialValue (x : ℝ) (N : ℕ) (ε z : ℂ) : ℂ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom Complex.ofRealHom z) ε
    (phaseExponential x N)

theorem phaseExponentialValue_eq_sum (x : ℝ) (N : ℕ) (ε z : ℂ) :
    phaseExponentialValue x N ε z =
      ∑ j ∈ Finset.range (N + 1), phaseDeviationValue x N ε z ^ j / (j.factorial : ℂ) := by
  simp [phaseExponentialValue, phaseExponential, phaseDeviationValue, map_sum,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_pow, div_eq_mul_inv, mul_comm]

/-- The actual exponential and the specified finite polynomial differ by a
controlled power of the phase deviation. -/
theorem norm_exp_phaseDeviation_sub_phaseExponential_le (x : ℝ) (N : ℕ) (ε z : ℂ) :
    ‖Complex.exp (phaseDeviationValue x N ε z) - phaseExponentialValue x N ε z‖ ≤
      ‖phaseDeviationValue x N ε z‖ ^ (N + 1) * Real.exp ‖phaseDeviationValue x N ε z‖ := by
  rw [phaseExponentialValue_eq_sum]
  exact Complex.norm_exp_sub_sum_le_norm_mul_exp _ _

theorem norm_exp_add_sub_exp_le (a r : ℂ) :
    ‖Complex.exp (a + r) - Complex.exp a‖ ≤
      Real.exp a.re * (‖r‖ * Real.exp ‖r‖) := by
  have h : ‖Complex.exp r - 1‖ ≤ ‖r‖ * Real.exp ‖r‖ := by
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp r 1
  rw [Complex.exp_add, ← mul_sub_one, norm_mul, Complex.norm_exp]
  exact mul_le_mul_of_nonneg_left h (le_of_lt (Real.exp_pos _))

/-- The exact normalized rational phase remainder, before exponentiation. -/
def normalizedPhaseError (x : ℝ) (N : ℕ) (ε z : ℂ) : ℂ :=
  (phaseConstant : ℂ) * reciprocalRemainder (saddleBeta x) (ε * z) (N + 2) / ε ^ 2

/-- A quantitative bound for exponentiating the actual phase expansion. The
right side contains only the explicit finite polynomial and rational remainder. -/
theorem norm_exp_complexSaddlePhase_sub_phaseExponential_le {x : ℝ} (hx : 0 < x)
    (N : ℕ) (ε z : ℂ) (hε : ε ≠ 0)
    (hw : (saddleBeta x : ℂ) + ε * z ≠ 0) :
    ‖Complex.exp ((complexSaddlePhase x ((saddleBeta x : ℂ) + ε * z) -
        (saddlePhase x (saddleBeta x) : ℂ)) / ε ^ 2) -
      Complex.exp ((saddleHessian x : ℂ) / 2 * z ^ 2) * phaseExponentialValue x N ε z‖ ≤
      Real.exp (((saddleHessian x : ℂ) / 2 * z ^ 2).re) *
        (Real.exp (phaseDeviationValue x N ε z).re *
            (‖normalizedPhaseError x N ε z‖ * Real.exp ‖normalizedPhaseError x N ε z‖) +
          ‖phaseDeviationValue x N ε z‖ ^ (N + 1) * Real.exp ‖phaseDeviationValue x N ε z‖) := by
  rw [complexSaddlePhase_exact_normalized hx ε z hε hw N]
  change ‖Complex.exp (((saddleHessian x : ℂ) / 2 * z ^ 2 + phaseDeviationValue x N ε z) +
      normalizedPhaseError x N ε z) - _‖ ≤ _
  rw [add_assoc, Complex.exp_add, ← mul_sub, norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
  calc
    ‖Complex.exp (phaseDeviationValue x N ε z + normalizedPhaseError x N ε z) -
        phaseExponentialValue x N ε z‖ ≤
      ‖Complex.exp (phaseDeviationValue x N ε z + normalizedPhaseError x N ε z) -
          Complex.exp (phaseDeviationValue x N ε z)‖ +
        ‖Complex.exp (phaseDeviationValue x N ε z) - phaseExponentialValue x N ε z‖ :=
      by
        simpa only [sub_add_sub_cancel] using (norm_add_le
          (Complex.exp (phaseDeviationValue x N ε z + normalizedPhaseError x N ε z) -
            Complex.exp (phaseDeviationValue x N ε z))
          (Complex.exp (phaseDeviationValue x N ε z) - phaseExponentialValue x N ε z))
    _ ≤ _ := add_le_add (norm_exp_add_sub_exp_le _ _)
      (norm_exp_phaseDeviation_sub_phaseExponential_le _ _ _ _)

/-- On the imaginary saddle direction, the Gaussian factor is exactly real. -/
theorem saddleGaussian_re (x t : ℝ) :
    (((saddleHessian x : ℂ) / 2 * ((t : ℂ) * Complex.I) ^ 2).re) =
      -(saddleHessian x / 2) * t ^ 2 := by
  have heq : (saddleHessian x : ℂ) / 2 * ((t : ℂ) * Complex.I) ^ 2 =
      ((-(saddleHessian x / 2) * t ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [heq]
  rfl

end BTZEntropy
