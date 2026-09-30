import BTZEntropy.Analytic.CoefficientNormProduct
import BTZEntropy.Analytic.LogPolynomial
import BTZEntropy.Analytic.LogPolynomialBound

/-!
# Uniform bound for the finite logarithm polynomial

A common bound for finitely many count coefficients gives an explicit bound
for the absolute coefficient sum of their finite logarithm polynomial. Thus
the polynomial Taylor remainder has a constant uniform in any parameters for
which those count coefficient bounds hold.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace BTZEntropy

/-- An explicit bound depending only on the truncation order and a common
bound for the count coefficients. -/
def logarithmPolynomialCoeffBound (P : ℕ) (M : ℝ) : ℝ :=
  ∑ j ∈ Finset.range P,
    |(-1 : ℝ) ^ j / (j + 1 : ℕ)| * ((P : ℝ) * M) ^ (j + 1)

theorem logarithmPolynomialCoeffBound_nonneg (P : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ logarithmPolynomialCoeffBound P M := by
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _)
    (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hM) _))

theorem correctionPolynomialCoeffNorm_le (u : ℕ → ℝ) (P : ℕ) (M : ℝ)
    (hu : ∀ n, 1 ≤ n → n ≤ P → |u n| ≤ M) :
    polynomialCoeffNorm (correctionPolynomial u P) ≤ (P : ℝ) * M := by
  unfold correctionPolynomial
  calc
    _ ≤ ∑ j ∈ Finset.range P, polynomialCoeffNorm (monomial (j + 1) (u (j + 1))) :=
      polynomialCoeffNorm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range P, M := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [polynomialCoeffNorm_monomial]
      exact hu (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)
    _ = (P : ℝ) * M := by simp

theorem logarithmPolynomialCoeffNorm_le (u : ℕ → ℝ) (P : ℕ) (M : ℝ)
    (hu : ∀ n, 1 ≤ n → n ≤ P → |u n| ≤ M) :
    polynomialCoeffNorm (logarithmPolynomial u P) ≤ logarithmPolynomialCoeffBound P M := by
  have hc := correctionPolynomialCoeffNorm_le u P M hu
  unfold logarithmPolynomial logarithmPolynomialCoeffBound
  refine (polynomialCoeffNorm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro j hj
  calc
    _ ≤ polynomialCoeffNorm (C ((-1 : ℝ) ^ j / (j + 1 : ℕ))) *
        polynomialCoeffNorm (correctionPolynomial u P ^ (j + 1)) :=
      polynomialCoeffNorm_mul_le _ _
    _ = |(-1 : ℝ) ^ j / (j + 1 : ℕ)| *
        polynomialCoeffNorm (correctionPolynomial u P ^ (j + 1)) := by
      rw [polynomialCoeffNorm_C]
    _ ≤ |(-1 : ℝ) ^ j / (j + 1 : ℕ)| *
        polynomialCoeffNorm (correctionPolynomial u P) ^ (j + 1) :=
      mul_le_mul_of_nonneg_left (polynomialCoeffNorm_pow_le _ _) (abs_nonneg _)
    _ ≤ |(-1 : ℝ) ^ j / (j + 1 : ℕ)| * ((P : ℝ) * M) ^ (j + 1) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (polynomialCoeffNorm_nonneg _) hc _) (abs_nonneg _)

theorem logarithmPolynomial_eval_sub_sum_range_le (u : ℕ → ℝ) (P : ℕ) (M : ℝ)
    (hu : ∀ n, 1 ≤ n → n ≤ P → |u n| ≤ M)
    {ε : ℝ} (hε : |ε| ≤ 1) :
    |(logarithmPolynomial u P).eval ε -
      ∑ n ∈ Finset.range (P + 1), (logarithmPolynomial u P).coeff n * ε ^ n| ≤
      logarithmPolynomialCoeffBound P M * |ε| ^ (P + 1) := by
  exact (polynomial_eval_sub_sum_range_le _ _ hε).trans
    (mul_le_mul_of_nonneg_right (logarithmPolynomialCoeffNorm_le u P M hu)
      (pow_nonneg (abs_nonneg ε) _))

end BTZEntropy
