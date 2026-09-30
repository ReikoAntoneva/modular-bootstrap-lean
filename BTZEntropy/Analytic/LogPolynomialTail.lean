import BTZEntropy.Analytic.PolynomialTail

/-!
# Tail of the designated entropy polynomial

The low-degree part of the composed finite logarithm is the independently
specified entropy correction. Its remaining terms have degree at least `P+1`.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace BTZEntropy

theorem logarithmPolynomial_prefix_eq_entropy
    (φ : ℝ → ℝ) (energyRatio : ℝ) (P : ℕ) (ε : ℝ) :
    (∑ n ∈ Finset.range (P + 1),
      (logarithmPolynomial (saddleCountCoefficient φ energyRatio) P).coeff n * ε ^ n) =
      ∑ j ∈ Finset.range P, entropyCoefficient φ energyRatio (j + 1) * ε ^ (j + 1) := by
  rw [Finset.sum_range_succ']
  simp only [logarithmPolynomial_coeff_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [logarithmPolynomial_coeff_eq_entropyCoefficient φ energyRatio
    (by have := Finset.mem_range.mp hj; omega)]

/-- The formal-log coefficient identification gives a quantitative evaluation remainder. -/
theorem logarithmPolynomial_eval_sub_entropy_le
    (φ : ℝ → ℝ) (energyRatio : ℝ) (P : ℕ) {ε : ℝ} (hε : |ε| ≤ 1) :
    |(logarithmPolynomial (saddleCountCoefficient φ energyRatio) P).eval ε -
        ∑ j ∈ Finset.range P, entropyCoefficient φ energyRatio (j + 1) * ε ^ (j + 1)| ≤
      ((logarithmPolynomial (saddleCountCoefficient φ energyRatio) P).sum
        fun _ a => |a|) * |ε| ^ (P + 1) := by
  rw [← logarithmPolynomial_prefix_eq_entropy]
  exact polynomial_eval_sub_sum_range_le _ _ hε

/-- A common bound for the saddle count coefficients controls the entropy
polynomial remainder uniformly in all remaining parameters. -/
theorem logarithmPolynomial_eval_sub_entropy_uniform_le
    (φ : ℝ → ℝ) (energyRatio : ℝ) (P : ℕ) (M : ℝ)
    (hu : ∀ n, 1 ≤ n → n ≤ P → |saddleCountCoefficient φ energyRatio n| ≤ M)
    {ε : ℝ} (hε : |ε| ≤ 1) :
    |(logarithmPolynomial (saddleCountCoefficient φ energyRatio) P).eval ε -
        ∑ j ∈ Finset.range P, entropyCoefficient φ energyRatio (j + 1) * ε ^ (j + 1)| ≤
      logarithmPolynomialCoeffBound P M * |ε| ^ (P + 1) := by
  rw [← logarithmPolynomial_prefix_eq_entropy]
  exact logarithmPolynomial_eval_sub_sum_range_le _ _ _ hu hε

end BTZEntropy
