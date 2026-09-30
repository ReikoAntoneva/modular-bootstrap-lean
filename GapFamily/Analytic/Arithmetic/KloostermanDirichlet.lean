import GapFamily.Analytic.Arithmetic.Kloosterman
import GapFamily.Analytic.Arithmetic.SelbergUnit
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# The Kloosterman Dirichlet series in its half-plane of convergence

The coefficient at zero is explicitly zero. At a positive denominator the
coefficient is the actual finite Kloosterman sum. The series has exponent
`2*s`; absolute convergence and holomorphic dependence are proved for
`1 < s.re`. This module makes no continuation claim.
-/

noncomputable section

namespace GapFamily.Analytic

/-- Actual finite Kloosterman coefficients, with an explicit zero coefficient. -/
def kloostermanCoefficient (m n : ℤ) (c : ℕ) : ℂ :=
  if c = 0 then 0 else kloostermanSum m n (c - 1)

@[simp] theorem kloostermanCoefficient_zero (m n : ℤ) :
    kloostermanCoefficient m n 0 = 0 := by
  simp [kloostermanCoefficient]

@[simp] theorem kloostermanCoefficient_succ (m n : ℤ) (k : ℕ) :
    kloostermanCoefficient m n (k + 1) = kloostermanSum m n k := by
  simp [kloostermanCoefficient]

/-- The elementary finite-sum bound in positive-denominator indexing. -/
theorem norm_kloostermanCoefficient_le (m n : ℤ) (c : ℕ) :
    ‖kloostermanCoefficient m n c‖ ≤ (c : ℝ) := by
  cases c with
  | zero => simp
  | succ k => simpa using norm_kloostermanSum_le m n k

/-- The actual Dirichlet series with the source exponent `2*s`. -/
def kloostermanDirichlet (m n : ℤ) (s : ℂ) : ℂ :=
  LSeries (kloostermanCoefficient m n) (2 * s)

/-- Frequency symmetry follows from the actual finite unit-inversion identity. -/
theorem kloostermanDirichlet_symm (m n : ℤ) (s : ℂ) :
    kloostermanDirichlet m n s = kloostermanDirichlet n m s := by
  have hcoeff : kloostermanCoefficient m n = kloostermanCoefficient n m := by
    funext c
    simp only [kloostermanCoefficient, kloostermanSum_symm m n]
  simp only [kloostermanDirichlet, hcoeff]

/-- A linear coefficient majorant gives genuine absolute convergence. -/
theorem kloostermanCoefficient_LSeriesSummable (m n : ℤ) {z : ℂ}
    (hz : 2 < z.re) : LSeriesSummable (kloostermanCoefficient m n) z := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 2) hz
  refine ⟨1, fun c _ => ?_⟩
  norm_num
  exact norm_kloostermanCoefficient_le m n c

/-- Summability at the exact doubled spectral parameter. -/
theorem kloostermanDirichlet_summable (m n : ℤ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (kloostermanCoefficient m n) (2 * s) := by
  apply kloostermanCoefficient_LSeriesSummable
  simp only [Complex.mul_re]
  norm_num
  linarith

/-- The coefficient growth bounds the actual abscissa of absolute convergence. -/
theorem kloostermanCoefficient_abscissa_le (m n : ℤ) :
    LSeries.abscissaOfAbsConv (kloostermanCoefficient m n) ≤ (2 : EReal) := by
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
    (f := kloostermanCoefficient m n) (x := 1)
    (show ∃ C : ℝ, ∀ c : ℕ, c ≠ 0 →
      ‖kloostermanCoefficient m n c‖ ≤ C * (c : ℝ) ^ (1 : ℝ) from
        ⟨1, fun c _ => by simpa using norm_kloostermanCoefficient_le m n c⟩)
  convert h using 1
  norm_num

@[simp] theorem kloostermanDirichlet_term_succ (m n : ℤ) (s : ℂ) (k : ℕ) :
    LSeries.term (kloostermanCoefficient m n) (2 * s) (k + 1) =
      kloostermanSum m n k / (k + 1 : ℂ) ^ (2 * s) := by
  simp [LSeries.term]

/-- The original positive-denominator series is summable. -/
theorem summable_kloostermanDirichlet (m n : ℤ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => kloostermanSum m n k / (k + 1 : ℂ) ^ (2 * s)) := by
  have h := (kloostermanDirichlet_summable m n hs).comp_injective
    (show Function.Injective (fun k : ℕ => k + 1) from fun _ _ h => Nat.add_right_cancel h)
  simpa only [Function.comp_def, kloostermanDirichlet_term_succ] using h

/-- Absolute convergence is explicit for the original positive-denominator series. -/
theorem summable_norm_kloostermanDirichlet (m n : ℤ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => ‖kloostermanSum m n k / (k + 1 : ℂ) ^ (2 * s)‖) :=
  (summable_kloostermanDirichlet m n hs).norm

/-- The L-series indexing agrees with the source's positive-denominator indexing. -/
theorem kloostermanDirichlet_eq_tsum (m n : ℤ) {s : ℂ} (hs : 1 < s.re) :
    kloostermanDirichlet m n s =
      ∑' k : ℕ, kloostermanSum m n k / (k + 1 : ℂ) ^ (2 * s) := by
  have hshift : HasSum
      (fun k : ℕ => LSeries.term (kloostermanCoefficient m n) (2 * s) (k + 1))
      (∑' k : ℕ, kloostermanSum m n k / (k + 1 : ℂ) ^ (2 * s)) := by
    simpa only [kloostermanDirichlet_term_succ] using
      (summable_kloostermanDirichlet m n hs).hasSum
  have hfull := hshift.zero_add
  simp only [LSeries.term_zero, zero_add] at hfull
  exact (kloostermanDirichlet_summable m n hs).hasSum.unique hfull

/-- The defined value is the sum of the actual positive-denominator series. -/
theorem kloostermanDirichlet_hasSum (m n : ℤ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => kloostermanSum m n k / (k + 1 : ℂ) ^ (2 * s))
      (kloostermanDirichlet m n s) := by
  rw [kloostermanDirichlet_eq_tsum m n hs]
  exact (summable_kloostermanDirichlet m n hs).hasSum

/-- Holomorphic dependence in the genuine half-plane of absolute convergence. -/
theorem kloostermanDirichlet_analyticAt (m n : ℤ) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (kloostermanDirichlet m n) s := by
  have hlt : LSeries.abscissaOfAbsConv (kloostermanCoefficient m n) <
      ((2 * s).re : EReal) := by
    apply lt_of_le_of_lt (kloostermanCoefficient_abscissa_le m n)
    have h : (2 : ℝ) < (2 * s).re := by
      simp only [Complex.mul_re]
      norm_num
      linarith
    exact EReal.coe_lt_coe h
  exact (LSeries_analyticOnNhd (kloostermanCoefficient m n) (2 * s) hlt).comp
    (analyticAt_const.mul analyticAt_id)

/-- A neighborhood-analytic statement on the entire open convergence half-plane. -/
theorem kloostermanDirichlet_analyticOnNhd (m n : ℤ) :
    AnalyticOnNhd ℂ (kloostermanDirichlet m n) {s : ℂ | 1 < s.re} :=
  fun _ hs => kloostermanDirichlet_analyticAt m n hs

/-- The source convention with a negative complex power, without any Gamma factor. -/
theorem kloostermanDirichlet_hasSum_neg_cpow (m n : ℤ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun c : ℕ => kloostermanSum m n c * (c + 1 : ℂ) ^ (-(2 * s)))
      (kloostermanDirichlet m n s) := by
  simpa only [Complex.cpow_neg, div_eq_mul_inv] using kloostermanDirichlet_hasSum m n hs

end GapFamily.Analytic
