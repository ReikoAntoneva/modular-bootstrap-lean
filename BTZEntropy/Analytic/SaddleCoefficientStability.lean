import BTZEntropy.Coefficient
import Mathlib.Algebra.Polynomial.Div

/-!
# Independence of finite coefficient truncation

The coefficient algorithm at a fixed order is unchanged when the common
Taylor truncation is increased. This connects a single finite integral Taylor
expansion with the separately defined coefficient at each order.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace BTZEntropy

private theorem coeff_mul_congr_le {R : Type*} [Semiring R]
    {p p' q q' : Polynomial R} {n : ℕ}
    (hp : ∀ j ≤ n, p.coeff j = p'.coeff j)
    (hq : ∀ j ≤ n, q.coeff j = q'.coeff j) :
    (p * q).coeff n = (p' * q').coeff n := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.mem_antidiagonal.mp hij
  rw [hp ij.1 (by omega), hq ij.2 (by omega)]

private theorem coeff_pow_congr_le {R : Type*} [Semiring R]
    {p q : Polynomial R} {N : ℕ} (h : ∀ j ≤ N, p.coeff j = q.coeff j)
    (k : ℕ) : ∀ j ≤ N, (p ^ k).coeff j = (q ^ k).coeff j := by
  induction k with
  | zero => simp
  | succ k ih =>
      intro j hj
      rw [pow_succ, pow_succ]
      exact coeff_mul_congr_le (fun l hl => ih l (hl.trans hj))
        (fun l hl => h l (hl.trans hj))

private theorem coeff_pow_eq_zero_of_const_eq_zero {R : Type*} [CommRing R]
    {p : Polynomial R} (hp : p.coeff 0 = 0) {n k : ℕ} (hnk : n < k) :
    (p ^ k).coeff n = 0 := by
  have hXdvd : (X : Polynomial R) ∣ p := Polynomial.X_dvd_iff.mpr hp
  exact Polynomial.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hXdvd k) n hnk

theorem amplitudeTaylor_coeff_stable (φ : ℝ → ℝ) (x : ℝ) {N M n : ℕ}
    (hNM : N ≤ M) (hn : n ≤ N) :
    (amplitudeTaylor φ x N).coeff n = (amplitudeTaylor φ x M).coeff n := by
  simp only [amplitudeTaylor, Polynomial.finsetSum_coeff]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hNM))
  intro j hjM hjN
  have hj : N < j := by simpa using hjN
  simp [Polynomial.coeff_monomial, show j ≠ n by omega]

theorem phaseDeviation_coeff_stable (x : ℝ) {N M n : ℕ}
    (hNM : N ≤ M) (hn : n ≤ N) :
    (phaseDeviation x N).coeff n = (phaseDeviation x M).coeff n := by
  simp only [phaseDeviation, Polynomial.finsetSum_coeff]
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro j hjM hjN
  have hj : N ≤ j := by simpa using hjN
  simp [Polynomial.coeff_monomial, show j + 1 ≠ n by omega]

@[simp] theorem phaseDeviation_coeff_zero (x : ℝ) (N : ℕ) :
    (phaseDeviation x N).coeff 0 = 0 := by
  simp [phaseDeviation, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

theorem phaseExponential_coeff_stable (x : ℝ) {N M n : ℕ}
    (hNM : N ≤ M) (hn : n ≤ N) :
    (phaseExponential x N).coeff n = (phaseExponential x M).coeff n := by
  simp only [phaseExponential, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  calc
    _ = ∑ j ∈ Finset.range (N + 1),
        C ((j.factorial : ℝ)⁻¹) * (phaseDeviation x M ^ j).coeff n := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [coeff_pow_congr_le (fun k hk => phaseDeviation_coeff_stable x hNM hk) j n hn]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hNM))
      intro j hjM hjN
      have hj : N < j := by simpa using hjN
      rw [coeff_pow_eq_zero_of_const_eq_zero (phaseDeviation_coeff_zero x M) (by omega), mul_zero]

theorem saddlePolynomial_coeff_stable (φ : ℝ → ℝ) (x : ℝ) {N M n : ℕ}
    (hNM : N ≤ M) (hn : n ≤ N) :
    (amplitudeTaylor φ x N * phaseExponential x N).coeff n =
      (amplitudeTaylor φ x M * phaseExponential x M).coeff n := by
  exact coeff_mul_congr_le
    (fun j hj => amplitudeTaylor_coeff_stable φ x hNM (hj.trans hn))
    (fun j hj => phaseExponential_coeff_stable x hNM (hj.trans hn))

/-- One common large truncation gives exactly the designated count coefficient. -/
theorem saddleCountCoefficient_eq_common_truncation (φ : ℝ → ℝ) (x : ℝ)
    (m N : ℕ) (hmN : 2 * m ≤ N) :
    saddleCountCoefficient φ x m =
      gaussianEvaluation (saddleHessian x)
        ((amplitudeTaylor φ x N * phaseExponential x N).coeff (2 * m)) /
          amplitude φ (saddleBeta x) := by
  unfold saddleCountCoefficient
  rw [saddlePolynomial_coeff_stable φ x hmN (le_refl _)]

end BTZEntropy
