import BTZEntropy.Coefficient

/-!
# Parity of the finite saddle coefficient algorithm

Every bivariate monomial has matching parity in the small parameter and the
saddle displacement. This property survives multiplication and finite sums.
Consequently, the Gaussian functional annihilates every odd parameter order.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace BTZEntropy

/-- The small parameter and displacement degrees have equal parity whenever a
bivariate coefficient is nonzero. -/
def HasMatchingCoefficientParity (p : Polynomial (Polynomial ℝ)) : Prop :=
  ∀ n k : ℕ, n % 2 ≠ k % 2 → (p.coeff n).coeff k = 0

theorem hasMatchingCoefficientParity_monomial (n k : ℕ) (a : ℝ)
    (h : n % 2 = k % 2) :
    HasMatchingCoefficientParity (monomial n (monomial k a)) := by
  intro i j hij
  by_cases hi : n = i
  · subst i
    by_cases hj : k = j
    · subst j
      exact (hij h).elim
    · simp [Polynomial.coeff_monomial, hj]
  · simp [Polynomial.coeff_monomial, hi]

theorem hasMatchingCoefficientParity_zero : HasMatchingCoefficientParity 0 := by
  simp [HasMatchingCoefficientParity]

theorem hasMatchingCoefficientParity_one : HasMatchingCoefficientParity 1 := by
  simpa using hasMatchingCoefficientParity_monomial 0 0 1 rfl

theorem hasMatchingCoefficientParity_C_C (a : ℝ) :
    HasMatchingCoefficientParity (C (C a)) := by
  simpa using hasMatchingCoefficientParity_monomial 0 0 a rfl

theorem HasMatchingCoefficientParity.sum {ι : Type*} (s : Finset ι)
    {p : ι → Polynomial (Polynomial ℝ)}
    (hp : ∀ i ∈ s, HasMatchingCoefficientParity (p i)) :
    HasMatchingCoefficientParity (∑ i ∈ s, p i) := by
  intro n k hnk
  simp only [Polynomial.finsetSum_coeff]
  exact Finset.sum_eq_zero (fun i hi => hp i hi n k hnk)

theorem HasMatchingCoefficientParity.mul {p q : Polynomial (Polynomial ℝ)}
    (hp : HasMatchingCoefficientParity p) (hq : HasMatchingCoefficientParity q) :
    HasMatchingCoefficientParity (p * q) := by
  intro n k hnk
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro ij hij
  have hij' := Finset.mem_antidiagonal.mp hij
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have hab' := Finset.mem_antidiagonal.mp hab
  by_cases hia : ij.1 % 2 = ab.1 % 2
  · have hjb : ij.2 % 2 ≠ ab.2 % 2 := by omega
    rw [hq _ _ hjb, mul_zero]
  · rw [hp _ _ hia, zero_mul]

theorem HasMatchingCoefficientParity.pow {p : Polynomial (Polynomial ℝ)}
    (hp : HasMatchingCoefficientParity p) (m : ℕ) :
    HasMatchingCoefficientParity (p ^ m) := by
  induction m with
  | zero => simpa using hasMatchingCoefficientParity_one
  | succ m ih => simpa [pow_succ] using ih.mul hp

theorem hasMatchingCoefficientParity_amplitudeTaylor (φ : ℝ → ℝ) (x : ℝ) (N : ℕ) :
    HasMatchingCoefficientParity (amplitudeTaylor φ x N) := by
  unfold amplitudeTaylor
  apply HasMatchingCoefficientParity.sum
  intro j hj
  exact hasMatchingCoefficientParity_monomial j j _ rfl

theorem hasMatchingCoefficientParity_phaseDeviation (x : ℝ) (N : ℕ) :
    HasMatchingCoefficientParity (phaseDeviation x N) := by
  unfold phaseDeviation
  apply HasMatchingCoefficientParity.sum
  intro j hj
  exact hasMatchingCoefficientParity_monomial (j + 1) (j + 3) _ (by omega)

theorem hasMatchingCoefficientParity_phaseExponential (x : ℝ) (N : ℕ) :
    HasMatchingCoefficientParity (phaseExponential x N) := by
  unfold phaseExponential
  apply HasMatchingCoefficientParity.sum
  intro j hj
  exact (hasMatchingCoefficientParity_C_C _).mul
    ((hasMatchingCoefficientParity_phaseDeviation x N).pow j)

/-- Gaussian evaluation of an odd outer coefficient is zero, because its inner
polynomial contains only odd displacement powers. -/
theorem HasMatchingCoefficientParity.gaussianEvaluation_eq_zero
    {p : Polynomial (Polynomial ℝ)} (hp : HasMatchingCoefficientParity p)
    (h : ℝ) {n : ℕ} (hn : Odd n) : gaussianEvaluation h (p.coeff n) = 0 := by
  unfold gaussianEvaluation Polynomial.sum
  apply Finset.sum_eq_zero
  intro k hk
  by_cases he : Even k
  · have hn' : n % 2 = 1 := Nat.odd_iff.mp hn
    have hk' : k % 2 = 0 := Nat.even_iff.mp he
    simp [hp n k (by omega)]
  · simp [imaginaryGaussianMoment, he]

/-- Every odd half-integer power cancels in the prescribed finite
Taylor--Gaussian algorithm. No positivity or analytic hypothesis is needed. -/
theorem gaussianEvaluation_saddle_odd (φ : ℝ → ℝ) (x : ℝ) (N : ℕ)
    {n : ℕ} (hn : Odd n) :
    gaussianEvaluation (saddleHessian x)
      ((amplitudeTaylor φ x N * phaseExponential x N).coeff n) = 0 :=
  ((hasMatchingCoefficientParity_amplitudeTaylor φ x N).mul
    (hasMatchingCoefficientParity_phaseExponential x N)).gaussianEvaluation_eq_zero _ hn

end BTZEntropy
