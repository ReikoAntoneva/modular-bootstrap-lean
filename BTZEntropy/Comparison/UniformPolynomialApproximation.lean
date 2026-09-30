import BTZEntropy.Comparison.RapidPolynomialApproximation
import BTZEntropy.Comparison.CosineDerivativeBound

/-! Uniform polynomial approximation constants from finitely many derivative bounds. -/

noncomputable section

open Set Polynomial
open scoped ContDiff

namespace BTZEntropy

/-- A universal finite constant; its numerical value is unnecessary for the approximation. -/
def integerSquareSum : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2

theorem integerSquareSum_nonneg : 0 ≤ integerSquareSum :=
  tsum_nonneg (fun _ => by positivity)

/-- Fourier comparison produces a bound shared by every function with the same
zeroth and `(P+2)`-th derivative bounds on one period. -/
theorem chebyshevCoefficientMass_le_of_cosineLine_bound {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (P : ℕ) {C₀ C : ℝ}
    (h₀ : ∀ t ∈ Icc (0 : ℝ) 1, ‖cosineLine h t‖ ≤ C₀)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv (P + 2) (cosineLine h) t‖ ≤ C) :
    chebyshevCoefficientMass (cosineCoefficient h hh.continuous) P ≤
      C₀ + (C / (2 * Real.pi) ^ (P + 2) * 2 ^ P) * integerSquareSum := by
  let D := C / (2 * Real.pi) ^ (P + 2) * 2 ^ P
  have hs := (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left D
  have hb := (hasSum_ite_eq (0 : ℤ) C₀).summable.add hs
  have hsum := summable_weighted_cosineCoefficient hh P
  have hbound : ∀ n : ℤ,
      |cosineCoefficient h hh.continuous n| * ((n.natAbs : ℝ) + 1) ^ P ≤
        (if n = 0 then C₀ else 0) + D * (1 / (n : ℝ) ^ 2) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simpa only [cosineCoefficient, fourierCoeff_cosineCircle_eq,
        Int.natAbs_zero, Nat.cast_zero, zero_add, one_pow, mul_one,
        ite_true, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, div_zero, mul_zero, add_zero] using
        (Complex.abs_re_le_norm _).trans (norm_fourierCoeffOn_le_of_bound h₀ 0)
    · have hnabs : (n.natAbs : ℝ) = ‖(n : ℝ)‖ := by
        rw [Real.norm_eq_abs, ← Int.cast_abs]
        exact Nat.cast_natAbs n
      dsimp [cosineCoefficient]
      rw [fourierCoeff_cosineCircle_eq, hnabs, ite_eq_right_iff.mpr (fun hn' => (hn hn').elim), zero_add]
      apply (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (by positivity)).trans
      simpa only [D, Real.norm_eq_abs, sq_abs, div_eq_mul_inv, one_mul] using
        weighted_fourierCoeffOn_le (cosineLine_contDiff hh) (cosineLine_periodic h) P hC hn
  have hc := hsum.tsum_le_tsum hbound hb
  rw [(hasSum_ite_eq (0 : ℤ) C₀).summable.tsum_add hs, tsum_ite_eq, tsum_mul_left] at hc
  exact hc

/-- Polynomial witnesses with a constant determined only by the stated finite
periodic derivative bounds. -/
theorem uniform_polynomial_approximation_of_cosineLine_bound {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (P : ℕ) {C₀ C : ℝ}
    (h₀ : ∀ t ∈ Icc (0 : ℝ) 1, ‖cosineLine h t‖ ≤ C₀)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv (P + 2) (cosineLine h) t‖ ≤ C)
    (k : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ k ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |h x - p.eval x| ≤
        (C₀ + (C / (2 * Real.pi) ^ (P + 2) * 2 ^ P) * integerSquareSum) /
          ((k : ℝ) + 1) ^ P := by
  refine ⟨chebyshevTruncation (cosineCoefficient h hh.continuous) k,
    Polynomial.degree_le_of_natDegree_le (chebyshevTruncation_natDegree_le _ _), ?_⟩
  intro x hx
  exact (chebyshevTruncation_error (summable_weighted_cosineCoefficient hh P)
    (fun _ hz => hasSum_cosineCoefficient h hh.continuous
      (summable_fourierCoeff_cosineCircle hh) hz) k hx).trans
    (div_le_div_of_nonneg_right
      (chebyshevCoefficientMass_le_of_cosineLine_bound hh P h₀ hC) (by positivity))

/-- A uniform approximation constant involving only finitely many derivative bounds. -/
def polynomialApproximationConstant (P : ℕ) (C : ℝ) : ℝ :=
  C + (P + 2).factorial * C * 2 ^ P * integerSquareSum

theorem polynomialApproximationConstant_nonneg (P : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ polynomialApproximationConstant P C := by
  unfold polynomialApproximationConstant
  have := integerSquareSum_nonneg
  positivity

/-- The uniform quantitative approximation theorem needed by the cell comparison.
Its constant depends only on a common bound through derivative order `P+2`, not
on the particular function or on the polynomial degree. -/
theorem polynomial_approximation_of_derivative_bound {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (P : ℕ) {C : ℝ}
    (hC : ∀ i : ℕ, i ≤ P + 2 → ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv i h x‖ ≤ C)
    (k : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ k ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |h x - p.eval x| ≤ polynomialApproximationConstant P C / ((k : ℝ) + 1) ^ P := by
  have h₀ : ∀ t ∈ Icc (0 : ℝ) 1, ‖cosineLine h t‖ ≤ C := by
    intro t _
    simpa using norm_iteratedDeriv_cosineLine_le hh 0
      (fun i hi => hC i (by omega)) t
  have hD : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv (P + 2) (cosineLine h) t‖ ≤
        (P + 2).factorial * C * (2 * Real.pi) ^ (P + 2) := by
    intro t _
    exact norm_iteratedDeriv_cosineLine_le hh (P + 2) hC t
  have heq : C + (((P + 2).factorial * C * (2 * Real.pi) ^ (P + 2)) /
      (2 * Real.pi) ^ (P + 2) * 2 ^ P) * integerSquareSum =
        polynomialApproximationConstant P C := by
    rw [mul_div_cancel_right₀ _ (by positivity : (2 * Real.pi) ^ (P + 2) ≠ 0)]
    rfl
  simpa only [heq] using uniform_polynomial_approximation_of_cosineLine_bound hh P h₀ hD k

end BTZEntropy
