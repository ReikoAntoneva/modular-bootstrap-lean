import BTZEntropy.Analytic.CoefficientNorm

/-!
# Product bound for the coefficient norm

The sum of absolute coefficients is submultiplicative. These estimates control
the coefficient tails of the finite logarithm polynomial.
-/

namespace BTZEntropy

open Polynomial
open scoped BigOperators

/-- The sum of absolute coefficients is submultiplicative. -/
theorem polynomialCoeffNorm_mul_le (p q : Polynomial ℝ) :
    polynomialCoeffNorm (p * q) ≤ polynomialCoeffNorm p * polynomialCoeffNorm q := by
  classical
  calc
    polynomialCoeffNorm (p * q) =
        polynomialCoeffNorm (∑ i ∈ p.support,
          ∑ j ∈ q.support, monomial (i + j) (p.coeff i * q.coeff j)) := by
      rw [Polynomial.mul_eq_sum_sum]
      rfl
    _ ≤ ∑ i ∈ p.support,
        polynomialCoeffNorm (∑ j ∈ q.support,
          monomial (i + j) (p.coeff i * q.coeff j)) := polynomialCoeffNorm_sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
        polynomialCoeffNorm (monomial (i + j) (p.coeff i * q.coeff j)) := by
      exact Finset.sum_le_sum fun _ _ => polynomialCoeffNorm_sum_le _ _
    _ = polynomialCoeffNorm p * polynomialCoeffNorm q := by
      simp_rw [polynomialCoeffNorm_monomial, abs_mul]
      unfold polynomialCoeffNorm Polynomial.sum
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]

/-- Powers obey the corresponding coefficient norm bound. -/
theorem polynomialCoeffNorm_pow_le (p : Polynomial ℝ) (n : ℕ) :
    polynomialCoeffNorm (p ^ n) ≤ polynomialCoeffNorm p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (polynomialCoeffNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ih (polynomialCoeffNorm_nonneg p))

end BTZEntropy
