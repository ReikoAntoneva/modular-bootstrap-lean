import GapFamily.Analytic.Arithmetic.SelbergGcd

/-!
# Common-frequency divisors
Finite Selberg divisor sums are reindexed by the fixed gcd of the two signed
frequencies. At least one frequency is nonzero, so that gcd has finitely many
positive divisors. The all-zero pair is kept separate.
-/

noncomputable section
namespace GapFamily.Analytic

theorem signed_common_divisor_iff (d : ℕ) (m n : ℤ) :
    (d : ℤ) ∣ m ∧ (d : ℤ) ∣ n ↔ d ∣ m.natAbs.gcd n.natAbs := by
  rw [Int.natCast_dvd, Int.natCast_dvd, Nat.dvd_gcd_iff]

theorem frequency_gcd_pos (m n : ℤ) (hne : m ≠ 0 ∨ n ≠ 0) :
    0 < m.natAbs.gcd n.natAbs := by
  rcases hne with hm | hn
  · exact Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (fun h => hm (Int.natAbs_eq_zero.mp h)))
  · exact Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (fun h => hn (Int.natAbs_eq_zero.mp h)))

theorem sum_divisor_subtype {c : ℕ} [NeZero c]
    {A : Type*} [AddCommMonoid A] (F : ℕ → A) :
    ∑ d : {d : ℕ // d ∣ c}, F d.1 = ∑ d ∈ c.divisors, F d := by
  let e : {d : ℕ // d ∈ c.divisors} ≃ {d : ℕ // d ∣ c} :=
    Equiv.subtypeEquivRight fun d => by simp [Nat.mem_divisors, NeZero.ne c]
  calc
    _ = ∑ d : {d : ℕ // d ∈ c.divisors}, F d.1 :=
      (e.sum_comp (fun d => F d.1)).symm
    _ = _ := by
      change ∑ d ∈ c.divisors.attach, F d.1 = _
      exact Finset.sum_attach _ _

theorem selberg_divisor_reindex {c : ℕ} [NeZero c] (m n : ℤ)
    (hne : m ≠ 0 ∨ n ≠ 0) {A : Type*} [AddCommMonoid A] (F : ℕ → A) :
    (∑ d : {d : ℕ // d ∣ c},
      if (d.1 : ℤ) ∣ m ∧ (d.1 : ℤ) ∣ n then F d.1 else 0) =
    ∑ d ∈ (m.natAbs.gcd n.natAbs).divisors, if d ∣ c then F d else 0 := by
  classical
  rw [sum_divisor_subtype (fun d => if (d : ℤ) ∣ m ∧ (d : ℤ) ∣ n then F d else 0)]
  simp_rw [signed_common_divisor_iff]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdc, _⟩, hdg⟩
    exact ⟨⟨hdg, (frequency_gcd_pos m n hne).ne'⟩, hdc⟩
  · rintro ⟨⟨hdg, _⟩, hdc⟩
    exact ⟨⟨hdc, NeZero.ne c⟩, hdg⟩

theorem common_frequency_divisor_pos {m n : ℤ} {d : ℕ}
    (hd : d ∈ (m.natAbs.gcd n.natAbs).divisors) : 0 < d :=
  Nat.pos_of_mem_divisors hd

end GapFamily.Analytic
