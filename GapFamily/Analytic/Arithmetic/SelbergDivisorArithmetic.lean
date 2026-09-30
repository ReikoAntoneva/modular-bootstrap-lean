import GapFamily.Analytic.Arithmetic.KloostermanDirichletDivisor
import Mathlib.Data.Int.CharZero

namespace GapFamily.Analytic.SelbergFiniteBound

/-- The actual integer reduced frequency is a product of exact signed quotients. -/
theorem normalized_frequency_eq_div_mul_div {m n : ℤ} {d : ℕ}
    (hd : d ∈ (m.natAbs.gcd n.natAbs).divisors) :
    m * n / (d : ℤ) ^ 2 = (m / (d : ℤ)) * (n / (d : ℤ)) := by
  obtain ⟨hdm, hdn⟩ := (signed_common_divisor_iff d m n).mpr (Nat.mem_divisors.mp hd).1
  have hd0 : (d : ℤ) ≠ 0 := by
    exact_mod_cast (common_frequency_divisor_pos hd).ne'
  apply Int.ediv_eq_of_eq_mul_left (pow_ne_zero 2 hd0)
  calc
    m * n = ((d : ℤ) * (m / d)) * ((d : ℤ) * (n / d)) := by
      rw [Int.mul_ediv_cancel' hdm, Int.mul_ediv_cancel' hdn]
    _ = ((m / d) * (n / d)) * (d : ℤ) ^ 2 := by ring

/-- Dividing both nonzero frequencies by a common divisor preserves a nonzero product. -/
theorem normalized_frequency_ne_zero {m n : ℤ} {d : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd : d ∈ (m.natAbs.gcd n.natAbs).divisors) :
    m * n / (d : ℤ) ^ 2 ≠ 0 := by
  obtain ⟨hdm, hdn⟩ := (signed_common_divisor_iff d m n).mpr (Nat.mem_divisors.mp hd).1
  have hdprod : (d : ℤ) ^ 2 ∣ m * n := by
    simpa only [pow_two] using mul_dvd_mul hdm hdn
  intro hz
  have hmul := Int.mul_ediv_cancel' hdprod
  rw [hz, mul_zero] at hmul
  exact mul_ne_zero hm hn hmul.symm

/-- Exact integer division gives the true reciprocal-square scaling of the real absolute value. -/
theorem abs_normalized_frequency_cast {m n : ℤ} {d : ℕ}
    (hd : d ∈ (m.natAbs.gcd n.natAbs).divisors) :
    |((m * n / (d : ℤ) ^ 2 : ℤ) : ℝ)| =
      |(m : ℝ) * (n : ℝ)| * (1 / (d : ℝ) ^ 2) := by
  obtain ⟨hdm, hdn⟩ := (signed_common_divisor_iff d m n).mpr (Nat.mem_divisors.mp hd).1
  have hdprod : (d : ℤ) ^ 2 ∣ m * n := by
    simpa only [pow_two] using mul_dvd_mul hdm hdn
  rw [Int.cast_div_charZero hdprod, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    abs_div, abs_of_nonneg (sq_nonneg (d : ℝ)), div_eq_mul_inv, one_div]

end GapFamily.Analytic.SelbergFiniteBound
