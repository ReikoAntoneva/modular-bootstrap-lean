import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! Quantitative Chebyshev truncation on the actual unit interval. -/

noncomputable section

open scoped BigOperators
open Set Polynomial

namespace BTZEntropy

/-- The shifted Chebyshev polynomial on `[0,1]`. -/
def unitChebyshev (n : ℤ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ n).comp (C 2 * X - C 1)

theorem unitChebyshev_natDegree_le (n : ℤ) :
    (unitChebyshev n).natDegree ≤ n.natAbs := by
  unfold unitChebyshev
  apply (Polynomial.natDegree_comp_le).trans
  rw [Polynomial.Chebyshev.natDegree_T]
  have h : (C (2 : ℝ) * X - C 1).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · simp
  simpa using Nat.mul_le_mul_left n.natAbs h

theorem unitChebyshev_eval (n : ℤ) (x : ℝ) :
    (unitChebyshev n).eval x = (Polynomial.Chebyshev.T ℝ n).eval (2 * x - 1) := by
  simp [unitChebyshev]

theorem abs_unitChebyshev_eval_le_one (n : ℤ) {x : ℝ} (hx : x ∈ Icc 0 1) :
    |(unitChebyshev n).eval x| ≤ 1 := by
  rw [unitChebyshev_eval]
  apply Polynomial.Chebyshev.abs_eval_T_real_le_one
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- Symmetric Fourier cutoff, interpreted as a genuine real polynomial. -/
def chebyshevTruncation (a : ℤ → ℝ) (k : ℕ) : ℝ[X] :=
  ∑ n ∈ Finset.Icc (-(k : ℤ)) k, C (a n) * unitChebyshev n

theorem chebyshevTruncation_natDegree_le (a : ℤ → ℝ) (k : ℕ) :
    (chebyshevTruncation a k).natDegree ≤ k := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  have hn' : n.natAbs ≤ k := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    exact abs_le.mpr (Finset.mem_Icc.mp hn)
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((unitChebyshev_natDegree_le n).trans hn')

theorem chebyshevTruncation_eval (a : ℤ → ℝ) (k : ℕ) (x : ℝ) :
    (chebyshevTruncation a k).eval x =
      ∑ n ∈ Finset.Icc (-(k : ℤ)) k, a n * (unitChebyshev n).eval x := by
  simp [chebyshevTruncation, Polynomial.eval_finsetSum]

/-- Weighted absolute coefficient mass; a finite derivative norm will bound it. -/
def chebyshevCoefficientMass (a : ℤ → ℝ) (P : ℕ) : ℝ :=
  ∑' n : ℤ, |a n| * ((n.natAbs : ℝ) + 1) ^ P

/-- The exact truncation estimate. It uses no regularity of any measured density. -/
theorem chebyshevTruncation_error {a : ℤ → ℝ} {f : ℝ → ℝ} {P : ℕ}
    (ha : Summable (fun n : ℤ => |a n| * ((n.natAbs : ℝ) + 1) ^ P))
    (hf : ∀ x ∈ Icc (0 : ℝ) 1,
      HasSum (fun n : ℤ => a n * (unitChebyshev n).eval x) (f x))
    (k : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |f x - (chebyshevTruncation a k).eval x| ≤
      chebyshevCoefficientMass a P / ((k : ℝ) + 1) ^ P := by
  let s : Finset ℤ := Finset.Icc (-(k : ℤ)) k
  let w : ℤ → ℝ := fun n => |a n| * ((n.natAbs : ℝ) + 1) ^ P
  have hw : Summable w := ha
  have hw0 : ∀ n, 0 ≤ w n := fun n => mul_nonneg (abs_nonneg _) (by positivity)
  have hden : 0 < ((k : ℝ) + 1) ^ P := by positivity
  have heq := (hf x hx).summable.sum_add_tsum_subtype_compl s
  rw [(hf x hx).tsum_eq] at heq
  rw [chebyshevTruncation_eval, ← heq, add_sub_cancel_left]
  change ‖∑' n : {n : ℤ // n ∉ s}, a n * (unitChebyshev n).eval x‖ ≤ _
  have hbound : ∀ n : {n : ℤ // n ∉ s},
      ‖a n * (unitChebyshev n).eval x‖ ≤ w n / ((k : ℝ) + 1) ^ P := by
    intro n
    have hn : k < n.val.natAbs := by
      by_contra h
      have he : |n.val| ≤ (k : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast (not_lt.mp h)
      exact n.property (Finset.mem_Icc.mpr (abs_le.mp he))
    have hpow : ((k : ℝ) + 1) ^ P ≤ ((n.val.natAbs : ℝ) + 1) ^ P := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt hn) 1
    rw [Real.norm_eq_abs, abs_mul]
    apply (mul_le_mul_of_nonneg_left (abs_unitChebyshev_eval_le_one n hx)
      (abs_nonneg _)).trans
    rw [mul_one, le_div_iff₀ hden]
    exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
  have hb := tsum_of_norm_bounded ((hw.subtype fun n => n ∉ s).div_const
    (((k : ℝ) + 1) ^ P)).hasSum hbound
  apply hb.trans
  rw [tsum_div_const]
  apply div_le_div_of_nonneg_right _ hden.le
  change (∑' n : {n : ℤ // n ∉ s}, w n) ≤ ∑' n : ℤ, w n
  exact Summable.tsum_subtype_le w {n | n ∉ s} hw0 hw

/-- Exact-degree polynomial witnesses, usable directly in moment cancellation. -/
theorem exists_polynomial_approximation_of_chebyshev {a : ℤ → ℝ} {f : ℝ → ℝ}
    {P : ℕ}
    (ha : Summable (fun n : ℤ => |a n| * ((n.natAbs : ℝ) + 1) ^ P))
    (hf : ∀ x ∈ Icc (0 : ℝ) 1,
      HasSum (fun n : ℤ => a n * (unitChebyshev n).eval x) (f x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∃ p : ℝ[X], p.degree ≤ k ∧
      ∀ x ∈ Icc (0 : ℝ) 1, |f x - p.eval x| ≤ C / ((k : ℝ) + 1) ^ P := by
  refine ⟨chebyshevCoefficientMass a P, tsum_nonneg (fun n => ?_), ?_⟩
  · positivity
  · intro k
    exact ⟨chebyshevTruncation a k,
      Polynomial.degree_le_of_natDegree_le (chebyshevTruncation_natDegree_le a k),
      fun x hx => chebyshevTruncation_error ha hf k hx⟩

end BTZEntropy
