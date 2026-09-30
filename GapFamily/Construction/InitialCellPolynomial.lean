import GapFamily.Analytic.Foundation.PolynomialExtrapolation
import GapFamily.Construction.InitialCellPolynomialMoment

/-!
# Polynomial extrapolation for the initial cell

The upper half of an interval controls a degree-`k` polynomial on the whole
interval with factor `6^k`. Positivity of the Chebyshev recurrence on `[1,3]`
retains the subtraction term and gives the rate needed by construction C7.
-/

open Set Polynomial

namespace GapFamily.Construction

/-- Chebyshev polynomials grow by at most a factor six at each degree on
the extrapolation interval associated with an upper half-cell. -/
theorem chebyshev_eval_le_six_pow (k : ℕ) (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 3) :
    (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval t ≤ (6 : ℝ) ^ k := by
  let T : ℕ → ℝ := fun n => (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval t
  have hrec (n : ℕ) : T (n + 2) = 2 * t * T (n + 1) - T n := by
    dsimp [T]
    simp only [Polynomial.Chebyshev.T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X]
  have hm (n : ℕ) : 1 ≤ T n ∧ T n ≤ T (n + 1) := by
    induction n with
    | zero => simpa [T] using ht.1
    | succ n hn =>
      have hn1 : 0 ≤ T (n + 1) := zero_le_one.trans (hn.1.trans hn.2)
      have hmul := mul_le_mul_of_nonneg_right ht.1 hn1
      rw [show n + 1 + 1 = n + 2 by omega, hrec]
      constructor <;> nlinarith [hn.1, hn.2]
  change T k ≤ (6 : ℝ) ^ k
  induction k using Nat.twoStepInduction with
  | zero => simp [T]
  | one => simpa [T] using ht.2.trans (by norm_num : (3 : ℝ) ≤ 6)
  | more n hn hn1 =>
    rw [hrec]
    calc
      _ ≤ 6 * T (n + 1) := by
        have hn0 : 0 ≤ T n := zero_le_one.trans (hm n).1
        have hn10 : 0 ≤ T (n + 1) := zero_le_one.trans (hm (n + 1)).1
        have hmul := mul_le_mul_of_nonneg_right ht.2 hn10
        nlinarith
      _ ≤ 6 * 6 ^ (n + 1) := mul_le_mul_of_nonneg_left hn1 (by norm_num)
      _ = 6 ^ (n + 2) := by ring

/-- Extrapolation from an upper half-cell with the sharp-enough exponential
factor used in the initial signed variation reserve. -/
theorem initialCell_polynomial_extrapolation (p : Polynomial ℝ) (k : ℕ)
    {a b S x : ℝ} (hab : a < b) (hdeg : p.natDegree ≤ k)
    (hbound : ∀ y ∈ Icc ((a + b) / 2) b, |p.eval y| ≤ S)
    (hx : x ∈ Icc a b) : |p.eval x| ≤ (6 : ℝ) ^ k * S := by
  have hmid : (a + b) / 2 < b := by linarith
  have hS : 0 ≤ S := (abs_nonneg (p.eval b)).trans (hbound b ⟨hmid.le, le_rfl⟩)
  by_cases hxm : (a + b) / 2 ≤ x
  · exact (hbound x ⟨hxm, hx.2⟩).trans
      (le_mul_of_one_le_left hS (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 6)))
  let m : ℝ := (a + b) / 2
  let q : Polynomial ℝ := p.comp (C ((m + b) / 2) - C ((b - m) / 2) * X)
  have hlin : (C ((m + b) / 2) - C ((b - m) / 2) * X : Polynomial ℝ).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le (by simp)
    simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le ((b - m) / 2) 1
  have hqdeg : q.natDegree ≤ k :=
    Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hlin).trans (by simpa using hdeg))
  have hqbound : ∀ t ∈ Icc (-1 : ℝ) 1, |q.eval t| ≤ S := by
    intro t ht
    simp only [q, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    apply hbound
    have hmul₁ := mul_le_mul_of_nonneg_left ht.1 (show 0 ≤ (b - m) / 2 by dsimp [m]; linarith)
    have hmul₂ := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (b - m) / 2 by dsimp [m]; linarith)
    dsimp [m] at *
    constructor <;> linarith
  have ht : (m + b - 2 * x) / (b - m) ∈ Icc (1 : ℝ) 3 := by
    have hden : 0 < b - m := by dsimp [m]; linarith
    constructor
    · apply (le_div_iff₀ hden).mpr
      dsimp [m] at *
      linarith
    · apply (div_le_iff₀ hden).mpr
      dsimp [m]
      linarith [hx.1]
  have hq := GapFamily.Analytic.polynomial_eval_abs_le_chebyshev q k hqdeg hS ht.1 hqbound
  have hinner : (m + b) / 2 - (b - m) / 2 * ((m + b - 2 * x) / (b - m)) = x := by
    field_simp [show b - m ≠ 0 from (sub_pos.mpr hmid).ne']
    ring
  have hqeval : q.eval ((m + b - 2 * x) / (b - m)) = p.eval x := by
    simp only [q, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, hinner]
  rw [hqeval] at hq
  exact hq.trans (mul_le_mul_of_nonneg_right (chebyshev_eval_le_six_pow k _ ht) hS)

/-- An upper-half polynomial bound controls the actual partition variation
on the entire initial cell with the same extrapolation factor. -/
theorem initialCell_polynomial_variation_le (p : Polynomial ℝ) (k : ℕ)
    {a b S : ℝ} (hab : a < b) (hdeg : p.natDegree ≤ k)
    (hbound : ∀ y ∈ Icc ((a + b) / 2) b, |p.eval y| ≤ S) :
    (eVariationOn p.eval (Icc a b)).toReal ≤
      4 * ((k : ℝ) + 1) ^ 3 * (6 : ℝ) ^ k * S := by
  calc
    _ ≤ 4 * ((k : ℝ) + 1) ^ 3 * ((6 : ℝ) ^ k * S) :=
      polynomial_variation_le_sup_bound p k hab hdeg
        (fun _ hx => initialCell_polynomial_extrapolation p k hab hdeg hbound hx)
    _ = _ := by ring

end GapFamily.Construction
