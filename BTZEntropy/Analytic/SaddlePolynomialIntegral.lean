import BTZEntropy.Analytic.SaddleCoefficientStability
import BTZEntropy.Analytic.SaddleParity
import BTZEntropy.Analytic.SaddleGaussian

/-!
# The finite Gaussian polynomial is the designated BTZ count series

Odd orders vanish exactly, and the remaining orders agree with the coefficient
definition independently of the common Taylor truncation.
-/

noncomputable section

open scoped BigOperators

namespace BTZEntropy

private theorem sum_range_pair {R : Type*} [AddCommMonoid R] (f : ℕ → R) (K : ℕ) :
    (∑ n ∈ Finset.range (2 * K), f n) =
      ∑ m ∈ Finset.range K, (f (2 * m) + f (2 * m + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [show 2 * (K + 1) = (2 * K + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [add_assoc]

theorem gaussian_saddlePolynomial_even (φ : ℝ → ℝ) (x : ℝ) (m N : ℕ)
    (hmN : 2 * m ≤ N) (hA : amplitude φ (saddleBeta x) ≠ 0) :
    gaussianEvaluation (saddleHessian x)
      ((amplitudeTaylor φ x N * phaseExponential x N).coeff (2 * m)) =
        amplitude φ (saddleBeta x) * saddleCountCoefficient φ x m := by
  rw [saddleCountCoefficient_eq_common_truncation φ x m N hmN]
  field_simp

/-- The complete finite Gaussian sum is precisely the prescribed normalized
count correction at `ε²`, rather than an independently chosen series. -/
theorem gaussian_saddlePolynomial_sum (φ : ℝ → ℝ) (x ε : ℝ) (P : ℕ)
    (hA : amplitude φ (saddleBeta x) ≠ 0) :
    (∑ n ∈ Finset.range (2 * P + 2), ε ^ n * gaussianEvaluation (saddleHessian x)
      ((amplitudeTaylor φ x (2 * P + 1) * phaseExponential x (2 * P + 1)).coeff n)) =
      amplitude φ (saddleBeta x) *
        (1 + (countCorrectionPolynomial φ x P).eval (ε ^ 2)) := by
  rw [show 2 * P + 2 = 2 * (P + 1) by omega, sum_range_pair]
  calc
    _ = ∑ m ∈ Finset.range (P + 1),
        ε ^ (2 * m) * (amplitude φ (saddleBeta x) * saddleCountCoefficient φ x m) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmP : m ≤ P := by simpa using Finset.mem_range.mp hm
      rw [gaussianEvaluation_saddle_odd φ x (2 * P + 1) (n := 2 * m + 1) (by exact ⟨m, rfl⟩),
        mul_zero, add_zero, gaussian_saddlePolynomial_even φ x m (2 * P + 1) (by omega) hA]
    _ = amplitude φ (saddleBeta x) *
        (∑ m ∈ Finset.range (P + 1), saddleCountCoefficient φ x m * (ε ^ 2) ^ m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [pow_mul]
      ring
    _ = _ := by
      rw [Finset.sum_range_succ']
      simp [saddleCountCoefficient_zero φ x hA, countCorrectionPolynomial,
        Polynomial.eval_finsetSum, Polynomial.eval_monomial, add_comm]

end BTZEntropy
