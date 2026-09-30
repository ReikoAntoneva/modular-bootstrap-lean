import BTZEntropy.Coefficient
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite logarithm polynomial

The coefficients through order `P` of the finite logarithm depend only on the
input coefficients through that same order. This links the finite polynomial
used in analytic Taylor estimates to the designated entropy coefficient.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace BTZEntropy

/-- Taking a power preserves agreement of all coefficients through a fixed order. -/
theorem polynomial_pow_coeff_eq_of_coeff_eq {R : Type*} [Semiring R]
    {p q : Polynomial R} {N : ℕ} (h : ∀ n ≤ N, p.coeff n = q.coeff n)
    (k n : ℕ) (hn : n ≤ N) : (p ^ k).coeff n = (q ^ k).coeff n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, Polynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Finset.mem_antidiagonal.mp hx
    rw [ih x.1 (by omega), h x.2 (by omega)]

/-- A zero constant term forces the `k`th power to start in degree at least `k`. -/
theorem polynomial_pow_coeff_eq_zero {R : Type*} [CommSemiring R]
    {p : Polynomial R} (hp : p.coeff 0 = 0) {k n : ℕ} (hn : n < k) :
    (p ^ k).coeff n = 0 := by
  apply Polynomial.X_pow_dvd_iff.mp _ n hn
  exact pow_dvd_pow_of_dvd (Polynomial.X_dvd_iff.mpr hp) k

/-- The positive-degree part of a prescribed coefficient sequence through order `N`. -/
def correctionPolynomial (u : ℕ → ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range N, monomial (j + 1) (u (j + 1))

/-- The finite logarithmic Taylor polynomial, composed with the correction polynomial. -/
def logarithmPolynomial (u : ℕ → ℝ) (P : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range P,
    C ((-1 : ℝ) ^ j / (j + 1 : ℕ)) * correctionPolynomial u P ^ (j + 1)

@[simp] theorem correctionPolynomial_coeff_zero (u : ℕ → ℝ) (N : ℕ) :
    (correctionPolynomial u N).coeff 0 = 0 := by
  simp [correctionPolynomial]

theorem correctionPolynomial_coeff_succ (u : ℕ → ℝ) (N n : ℕ) :
    (correctionPolynomial u N).coeff (n + 1) = if n < N then u (n + 1) else 0 := by
  simp [correctionPolynomial, Polynomial.coeff_monomial]

theorem correctionPolynomial_coeff_eq (u : ℕ → ℝ) {N n : ℕ}
    (hn : 0 < n) (hN : n ≤ N) : (correctionPolynomial u N).coeff n = u n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp [correctionPolynomial_coeff_succ, show n < N by omega]

theorem correctionPolynomial_coeff_stable (u : ℕ → ℝ) {M N n : ℕ}
    (hM : n ≤ M) (hN : n ≤ N) :
    (correctionPolynomial u M).coeff n = (correctionPolynomial u N).coeff n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [correctionPolynomial_coeff_eq u (by omega) hM,
      correctionPolynomial_coeff_eq u (by omega) hN]

theorem correctionPolynomial_pow_coeff_stable (u : ℕ → ℝ) {M N n : ℕ}
    (hM : n ≤ M) (hN : n ≤ N) (k : ℕ) :
    (correctionPolynomial u M ^ k).coeff n =
      (correctionPolynomial u N ^ k).coeff n := by
  apply polynomial_pow_coeff_eq_of_coeff_eq (N := n) ?_ k n le_rfl
  intro j hj
  exact correctionPolynomial_coeff_stable u (hj.trans hM) (hj.trans hN)

theorem correctionPolynomial_pow_coeff_eq_zero (u : ℕ → ℝ) (N : ℕ)
    {k n : ℕ} (hn : n < k) : (correctionPolynomial u N ^ k).coeff n = 0 := by
  exact polynomial_pow_coeff_eq_zero (correctionPolynomial_coeff_zero u N) hn

@[simp] theorem logarithmPolynomial_coeff_zero (u : ℕ → ℝ) (P : ℕ) :
    (logarithmPolynomial u P).coeff 0 = 0 := by
  simp only [logarithmPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_eq_zero
  intro j hj
  rw [correctionPolynomial_pow_coeff_eq_zero u P (by omega), mul_zero]

/-- At degree `n ≤ P`, truncating the input and the logarithmic sum at `n`
does not change the coefficient. -/
theorem logarithmPolynomial_coeff (u : ℕ → ℝ) {P n : ℕ} (hn : n ≤ P) :
    (logarithmPolynomial u P).coeff n =
      ∑ j ∈ Finset.range n, ((-1 : ℝ) ^ j / (j + 1 : ℕ)) *
        (correctionPolynomial u n ^ (j + 1)).coeff n := by
  calc
    (logarithmPolynomial u P).coeff n =
        ∑ j ∈ Finset.range P, ((-1 : ℝ) ^ j / (j + 1 : ℕ)) *
          (correctionPolynomial u n ^ (j + 1)).coeff n := by
      simp only [logarithmPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [correctionPolynomial_pow_coeff_stable u hn le_rfl (j + 1)]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.range_mono hn)
      intro j hj hjn
      have : n ≤ j := by simpa using hjn
      rw [correctionPolynomial_pow_coeff_eq_zero u n (by omega), mul_zero]

/-- The analytic finite logarithm uses exactly the preassigned finite algorithm. -/
theorem logarithmPolynomial_coeff_eq_logarithmicCoefficient
    (φ : ℝ → ℝ) (energyRatio : ℝ) {P n : ℕ} (hn : n ≤ P) :
    (logarithmPolynomial (saddleCountCoefficient φ energyRatio) P).coeff n =
      logarithmicCoefficient φ energyRatio n := by
  simpa only [logarithmicCoefficient, countCorrectionPolynomial, correctionPolynomial] using
    logarithmPolynomial_coeff (saddleCountCoefficient φ energyRatio) hn

theorem logarithmPolynomial_coeff_eq_entropyCoefficient
    (φ : ℝ → ℝ) (energyRatio : ℝ) {P n : ℕ} (hn : n + 1 ≤ P) :
    (logarithmPolynomial (saddleCountCoefficient φ energyRatio) P).coeff (n + 1) =
      entropyCoefficient φ energyRatio (n + 1) :=
  logarithmPolynomial_coeff_eq_logarithmicCoefficient φ energyRatio hn

@[simp] theorem correctionPolynomial_eval (u : ℕ → ℝ) (P : ℕ) (ε : ℝ) :
    (correctionPolynomial u P).eval ε =
      ∑ j ∈ Finset.range P, u (j + 1) * ε ^ (j + 1) := by
  simp [correctionPolynomial, Polynomial.eval_finsetSum]

theorem logarithmPolynomial_eval (u : ℕ → ℝ) (P : ℕ) (ε : ℝ) :
    (logarithmPolynomial u P).eval ε =
      ∑ j ∈ Finset.range P, ((-1 : ℝ) ^ j / (j + 1 : ℕ)) *
        ((correctionPolynomial u P).eval ε) ^ (j + 1) := by
  simp [logarithmPolynomial, Polynomial.eval_finsetSum]

end BTZEntropy
