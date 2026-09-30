import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralSelbergCleared
import GapFamily.Analytic.Arithmetic.SelbergFiniteBound

/-! The finite Selberg identity for the actual canonical threshold zeta values. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCentralZeta
open PoincareFourierContinuation PoincareCentralFactor
open SelbergFiniteBound SelbergClearedProduct

/-- The actual central values obey Selberg's finite signed-frequency identity.
Only nonzero frequencies are assumed; the identity is obtained from the genuine
Dirichlet region and cancellation of the proved nonzero threshold factors. -/
theorem centralZeta_zero_selberg (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    centralZeta m n 0 = ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
      centralZeta (m * n / (d : ℤ) ^ 2) 1 0 := by
  classical
  let s := (m.natAbs.gcd n.natAbs).divisors
  have hclear := centralNumerator_selberg_cleared m n hm hn
    (zero_mem_horizontalFourierDomain 1 zero_lt_one)
  simp only [mul_zero, Complex.cpow_zero, one_mul] at hclear
  exact finite_sum_of_cleared_identity s
    (D0 := centralFourierFactor 1 m 0) (Z0 := centralZeta m n 0)
    (A0 := centralNumerator 1 zero_lt_one m n 0)
    (D := fun d => centralFourierFactor 1 (m * n / (d : ℤ) ^ 2) 0)
    (Z := fun d => centralZeta (m * n / (d : ℤ) ^ 2) 1 0)
    (A := fun d => centralNumerator 1 zero_lt_one (m * n / (d : ℤ) ^ 2) 1 0)
    (centralFourierFactor_zero_ne_zero zero_lt_one hm)
    (fun d hd => centralFourierFactor_zero_ne_zero zero_lt_one
      (normalized_frequency_ne_zero hm hn hd))
    (by simpa only [mul_comm] using
      (centralZeta_zero_mul_factor 1 zero_lt_one m n hm).symm)
    (fun d hd => by simpa only [mul_comm] using
      (centralZeta_zero_mul_factor 1 zero_lt_one _ 1
        (normalized_frequency_ne_zero hm hn hd)).symm)
    hclear

/-- Exact signed division gives the source's quotient-product form of the
actual threshold Selberg identity. -/
theorem centralZeta_zero_selberg_div_mul_div (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    centralZeta m n 0 = ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors,
      centralZeta ((m / (d : ℤ)) * (n / (d : ℤ))) 1 0 := by
  rw [centralZeta_zero_selberg m n hm hn]
  apply Finset.sum_congr rfl
  intro d hd
  rw [normalized_frequency_eq_div_mul_div hd]

/-- With the actual central Selberg identity now proved, only a normalized
central bound is needed for the universal two-frequency estimate. -/
theorem centralZeta_zero_norm_le {C : ℝ} (hC : 0 ≤ C)
    (hbase : ∀ N : ℤ, N ≠ 0 → ‖centralZeta N 1 0‖ ≤ C * |(N : ℝ)|)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ‖centralZeta m n 0‖ ≤ (C * (Real.pi ^ 2 / 6)) * |(m : ℝ) * (n : ℝ)| :=
  norm_le_of_finite_selberg (fun j J => centralZeta j J 0) hC hbase hm hn
    (centralZeta_zero_selberg m n hm hn)

/-- The remaining normalized central estimate is enough for one positive
constant uniform in both nonzero spins. -/
theorem exists_uniform_centralZeta_zero_bound
    (hbase : ∃ C : ℝ, 0 < C ∧
      ∀ N : ℤ, N ≠ 0 → ‖centralZeta N 1 0‖ ≤ C * |(N : ℝ)|) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ m n : ℤ, m ≠ 0 → n ≠ 0 →
      ‖centralZeta m n 0‖ ≤ C' * |(m : ℝ) * (n : ℝ)| :=
  exists_uniform_bound_of_finite_selberg (fun j J => centralZeta j J 0) hbase
    centralZeta_zero_selberg

end GapFamily.Analytic.PoincareCentralZeta
