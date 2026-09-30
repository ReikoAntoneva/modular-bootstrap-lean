import GapFamily.Analytic.Arithmetic.SelbergDivisorArithmetic
import GapFamily.Analytic.Arithmetic.SelbergFiniteZeta

/-!
Finite central Selberg arithmetic only. The reduced frequency matches the
actual convergent Selberg identity. Any identity for continued central values
is an explicit premise; this module does not assert analytic continuation.
-/

noncomputable section
namespace GapFamily.Analytic.SelbergFiniteBound

/-- A uniform bound for normalized nonzero frequencies controls the finite
Selberg divisor sum with the actual universal Basel multiplier. -/
theorem norm_sum_normalized_frequency_le (z : ℤ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hz : ∀ N : ℤ, N ≠ 0 → ‖z N‖ ≤ C * |(N : ℝ)|)
    {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ‖∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
      z (m * n / (d : ℤ) ^ 2)‖ ≤
      (C * (Real.pi ^ 2 / 6)) * |(m : ℝ) * (n : ℝ)| := by
  classical
  let D := (m.natAbs.gcd n.natAbs).divisors
  calc
    _ ≤ ∑ d ∈ D, ‖z (m * n / (d : ℤ) ^ 2)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ D, C * |(m : ℝ) * (n : ℝ)| * (1 / (d : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro d hd
      calc
        _ ≤ C * |((m * n / (d : ℤ) ^ 2 : ℤ) : ℝ)| :=
          hz _ (normalized_frequency_ne_zero hm hn hd)
        _ = _ := by rw [abs_normalized_frequency_cast hd]; ring
    _ = C * |(m : ℝ) * (n : ℝ)| * (∑ d ∈ D, 1 / (d : ℝ) ^ 2) :=
      (Finset.mul_sum ..).symm
    _ ≤ C * |(m : ℝ) * (n : ℝ)| * (Real.pi ^ 2 / 6) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_sq_le_zeta_two D)
        (mul_nonneg hC (abs_nonneg _))
    _ = _ := by ring

/-- Conditional only on the explicitly supplied finite central identity;
The bound makes no continuation or threshold matching claim. -/
theorem norm_le_of_finite_selberg (Z : ℤ → ℤ → ℂ) {C : ℝ}
    (hC : 0 ≤ C)
    (hbase : ∀ N : ℤ, N ≠ 0 → ‖Z N 1‖ ≤ C * |(N : ℝ)|)
    {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hselberg : Z m n =
      ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
        Z (m * n / (d : ℤ) ^ 2) 1) :
    ‖Z m n‖ ≤ (C * (Real.pi ^ 2 / 6)) * |(m : ℝ) * (n : ℝ)| := by
  rw [hselberg]
  exact norm_sum_normalized_frequency_le (fun N => Z N 1) hC hbase hm hn

/-- The literal quotient-product version of the finite identity has exactly
the same bound; common signed divisibility justifies the integer reindexing. -/
theorem norm_le_of_finite_selberg_div_mul_div (Z : ℤ → ℤ → ℂ) {C : ℝ}
    (hC : 0 ≤ C)
    (hbase : ∀ N : ℤ, N ≠ 0 → ‖Z N 1‖ ≤ C * |(N : ℝ)|)
    {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hselberg : Z m n =
      ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
        Z ((m / (d : ℤ)) * (n / (d : ℤ))) 1) :
    ‖Z m n‖ ≤ (C * (Real.pi ^ 2 / 6)) * |(m : ℝ) * (n : ℝ)| := by
  apply norm_le_of_finite_selberg Z hC hbase hm hn
  rw [hselberg]
  apply Finset.sum_congr rfl
  intro d hd
  rw [normalized_frequency_eq_div_mul_div hd]

/-- A single positive normalized-frequency constant yields a single positive
constant for every pair of nonzero frequencies, assuming all finite identities. -/
theorem exists_uniform_bound_of_finite_selberg (Z : ℤ → ℤ → ℂ)
    (hbase : ∃ C : ℝ, 0 < C ∧
      ∀ N : ℤ, N ≠ 0 → ‖Z N 1‖ ≤ C * |(N : ℝ)|)
    (hselberg : ∀ m n : ℤ, m ≠ 0 → n ≠ 0 → Z m n =
      ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
        Z (m * n / (d : ℤ) ^ 2) 1) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ m n : ℤ, m ≠ 0 → n ≠ 0 →
      ‖Z m n‖ ≤ C' * |(m : ℝ) * (n : ℝ)| := by
  obtain ⟨C, hC, hbase⟩ := hbase
  refine ⟨C * (Real.pi ^ 2 / 6), mul_pos hC (by positivity), ?_⟩
  intro m n hm hn
  exact norm_le_of_finite_selberg Z hC.le hbase hm hn (hselberg m n hm hn)

end GapFamily.Analytic.SelbergFiniteBound
