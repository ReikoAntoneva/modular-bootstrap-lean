import GapFamily.Analytic.Arithmetic.KloostermanDirichlet
import GapFamily.Analytic.Arithmetic.KloostermanDirichletDilation
import GapFamily.Analytic.Arithmetic.KloostermanDirichletDivisor
import GapFamily.Analytic.Arithmetic.Selberg
import GapFamily.Analytic.Arithmetic.SelbergUnit
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Selberg's identity for convergent Kloosterman Dirichlet series

The finite identity is first reindexed by the fixed positive divisors of the
frequency gcd. Every dilated series is genuinely summable before linearity of
the infinite sums is used. No continued value at one half is asserted.
-/

noncomputable section
namespace GapFamily.Analytic

/-- Coefficient-level Selberg decomposition with a fixed finite divisor set. -/
theorem kloostermanCoefficient_selberg (m n : ℤ) (hne : m ≠ 0 ∨ n ≠ 0) (c : ℕ) :
    kloostermanCoefficient m n c =
      ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
        (d : ℂ) * dirichletDilation d
          (kloostermanCoefficient (m * n / (d : ℤ) ^ 2) 1) c := by
  classical
  by_cases hc : c = 0
  · subst c
    simp [dirichletDilation]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
  rw [kloostermanCoefficient_succ, kloostermanSum_selberg]
  let F : ℕ → ℂ := fun d =>
    (d : ℂ) * kloostermanCoefficient (m * n / (d : ℤ) ^ 2) 1 ((k + 1) / d)
  calc
    _ = ∑ d : {d : ℕ // d ∣ k + 1},
        if (d.val : ℤ) ∣ m ∧ (d.val : ℤ) ∣ n then F d.val else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      split_ifs
      · dsimp [F]
        rw [kloostermanCoefficient, ite_eq_right (NeZero.ne ((k + 1) / d.val))]
      · rfl
    _ = ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
        if d ∣ k + 1 then F d else 0 := selberg_divisor_reindex m n hne F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d ∣ k + 1 <;> simp [dirichletDilation, hd, F]

/-- Function-level form suitable for the library's finite L-series linearity. -/
theorem kloostermanCoefficient_eq_sum_dilation (m n : ℤ) (hne : m ≠ 0 ∨ n ≠ 0) :
    kloostermanCoefficient m n =
      ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
        (d : ℂ) • dirichletDilation d
          (kloostermanCoefficient (m * n / (d : ℤ) ^ 2) 1) := by
  funext c
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    kloostermanCoefficient_selberg m n hne c

/-- Every summand of the finite divisor expansion defines a convergent L-series. -/
theorem kloostermanDirichlet_divisor_summable (m n : ℤ) {s : ℂ}
    (hs : 1 < s.re) {d : ℕ} (hd : d ∈ (m.natAbs.gcd n.natAbs).divisors) :
    LSeriesSummable ((d : ℂ) • dirichletDilation d
      (kloostermanCoefficient (m * n / (d : ℤ) ^ 2) 1)) (2 * s) :=
  (lSeriesSummable_dirichletDilation d (common_frequency_divisor_pos hd) _ _
    (kloostermanDirichlet_summable _ _ hs)).smul _

/-- Selberg's identity throughout the genuine common convergence half-plane,
before combining the elementary complex powers. -/
theorem kloostermanDirichlet_selberg_mul (m n : ℤ) (hne : m ≠ 0 ∨ n ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    kloostermanDirichlet m n s =
      ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
        (d : ℂ) * (d : ℂ) ^ (-(2 * s)) *
          kloostermanDirichlet (m * n / (d : ℤ) ^ 2) 1 s := by
  unfold kloostermanDirichlet
  rw [kloostermanCoefficient_eq_sum_dilation m n hne]
  rw [LSeries_sum (fun d hd => kloostermanDirichlet_divisor_summable m n hs hd)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [LSeries_smul, lSeries_dirichletDilation d (common_frequency_divisor_pos hd)]
  ring

/-- The finite Selberg divisor identity for the actual Kloosterman Dirichlet
series. The exponent and signs agree with the original arithmetic statement. -/
theorem kloostermanDirichlet_selberg (m n : ℤ) (hne : m ≠ 0 ∨ n ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    kloostermanDirichlet m n s =
      ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
        (d : ℂ) ^ (1 - 2 * s) *
          kloostermanDirichlet (m * n / (d : ℤ) ^ 2) 1 s := by
  rw [kloostermanDirichlet_selberg_mul m n hne hs]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℂ) ≠ 0 := by
    exact_mod_cast (common_frequency_divisor_pos hd).ne'
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hd0, Complex.cpow_one]

/-- The source's normalized-first-frequency form of the same convergent identity. -/
theorem kloostermanDirichlet_selberg_one_left (m n : ℤ) (hne : m ≠ 0 ∨ n ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    kloostermanDirichlet m n s =
      ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
        (d : ℂ) ^ (1 - 2 * s) *
          kloostermanDirichlet 1 (m * n / (d : ℤ) ^ 2) s := by
  rw [kloostermanDirichlet_selberg m n hne hs]
  apply Finset.sum_congr rfl
  intro d _
  rw [kloostermanDirichlet_symm (m * n / (d : ℤ) ^ 2) 1]

/-- The finite divisor formula supplies the sum of the actual series, with
absolute convergence already certified in the same half-plane. -/
theorem kloostermanDirichlet_selberg_hasSum (m n : ℤ) (hne : m ≠ 0 ∨ n ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun c : ℕ => kloostermanSum m n c / (c + 1 : ℂ) ^ (2 * s))
      (∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
        (d : ℂ) ^ (1 - 2 * s) *
          kloostermanDirichlet 1 (m * n / (d : ℤ) ^ 2) s) := by
  rw [← kloostermanDirichlet_selberg_one_left m n hne hs]
  exact kloostermanDirichlet_hasSum m n hs

/-- A single zero frequency is retained: the divisor factor is finite whenever
the other frequency is nonzero. -/
theorem kloostermanDirichlet_zero_left (n : ℤ) (hn : n ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    kloostermanDirichlet 0 n s =
      (∑ d ∈ n.natAbs.divisors, (d : ℂ) ^ (1 - 2 * s)) *
        kloostermanDirichlet 0 1 s := by
  have h := kloostermanDirichlet_selberg 0 n (Or.inr hn) hs
  simpa only [Int.natAbs_zero, Nat.gcd_zero_left, zero_mul, Int.zero_ediv,
    Finset.sum_mul] using h

theorem kloostermanDirichlet_zero_right (m : ℤ) (hm : m ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    kloostermanDirichlet m 0 s =
      (∑ d ∈ m.natAbs.divisors, (d : ℂ) ^ (1 - 2 * s)) *
        kloostermanDirichlet 0 1 s := by
  rw [kloostermanDirichlet_symm m 0]
  exact kloostermanDirichlet_zero_left m hm hs

end GapFamily.Analytic
