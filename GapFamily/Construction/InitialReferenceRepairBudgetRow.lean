import GapFamily.Analytic.Kernel.LowBandSpinSet

/-!
# Finite row factor in the initial repair budget

The initial rows include both endpoints of the integer spin window. Their
cardinality costs one additional polynomial degree in the charge scale.
-/

noncomputable section

open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

/-- All integer rows up to and including the initial reference threshold. -/
def initialReferenceRows (T : ℕ) : Finset ℤ :=
  lowBandSpinSet ((T : ℝ) + 1)

@[simp] theorem mem_initialReferenceRows (T : ℕ) (j : ℤ) :
    j ∈ initialReferenceRows T ↔ |(j : ℝ)| ≤ (T : ℝ) := by
  simp only [initialReferenceRows, mem_lowBandSpinSet]
  exact_mod_cast (Int.lt_add_one_iff : |j| < (T : ℤ) + 1 ↔ |j| ≤ (T : ℤ))

/-- The closed integer spin window has a linear cardinality bound. -/
theorem initialReferenceRows_card_le (T : ℕ) :
    ((initialReferenceRows T).card : ℝ) ≤ 5 * ((T : ℝ) + 1) :=
  lowBandSpinSet_card_le _ (by have : (0 : ℝ) ≤ T := Nat.cast_nonneg T; linarith)

/-- In the ordered integer construction, the number of initial rows is
bounded by ten times one plus the physical charge. -/
theorem initialReferenceRows_card_le_charge {R₀ R s n : ℕ}
    (hR : 16 * R₀ ≤ R) (hs : 1 ≤ s) :
    ((initialReferenceRows (R₀ * n)).card : ℝ) ≤
      10 * (1 + (R : ℝ) * (s : ℝ) ^ 2 * n) := by
  have hR₀R : R₀ ≤ R := by omega
  have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs
  have hRR : R ≤ R * s ^ 2 := by nlinarith
  have hnat : R₀ * n ≤ R * s ^ 2 * n :=
    Nat.mul_le_mul_right n (hR₀R.trans hRR)
  have hcharge : ((R₀ * n : ℕ) : ℝ) ≤ (R : ℝ) * (s : ℝ) ^ 2 * n := by
    exact_mod_cast hnat
  have hcard := initialReferenceRows_card_le (R₀ * n)
  nlinarith

/-- A row count linear in the polynomial base raises the repair degree by one. -/
theorem initialReference_fintype_sum_prefactor
    {ι : Type*} [Fintype ι] {C X : ℝ} (p : ℕ)
    (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hcard : (Fintype.card ι : ℝ) ≤ 10 * X)
    (f : ι → ℝ) (hf : ∀ i, f i ≤ C * X ^ p) :
    ∑ i, f i ≤ (10 * C) * X ^ (p + 1) := by
  calc
    ∑ i, f i ≤ ∑ _i : ι, C * X ^ p :=
      Finset.sum_le_sum (fun i _ => hf i)
    _ = (Fintype.card ι : ℝ) * (C * X ^ p) := by simp
    _ ≤ (10 * X) * (C * X ^ p) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (10 * C) * X ^ (p + 1) := by rw [pow_succ]; ring

/-- A uniform per-row polynomial estimate sums over the actual initial
row subtype with one extra degree and the fixed coefficient ten. -/
theorem sum_le_initialReferenceRows_polynomial (T : ℕ) {a C X : ℝ} (p : ℕ)
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hcard : ((initialReferenceRows T).card : ℝ) ≤ 10 * (1 + a))
    (hX : 1 + a ≤ X)
    (f : ↥(initialReferenceRows T) → ℝ) (hf : ∀ j, f j ≤ C * X ^ p) :
    ∑ j, f j ≤ (10 * C) * X ^ (p + 1) := by
  apply initialReference_fintype_sum_prefactor p hC (by linarith) _ f hf
  simpa only [Fintype.card_coe] using
    hcard.trans (mul_le_mul_of_nonneg_left hX (by norm_num))

/-- The ordered integer parameters supply the row count premise directly. -/
theorem sum_le_initialReferenceRows_polynomial_charge
    {R₀ R s n : ℕ} {C X : ℝ} (p : ℕ)
    (hR : 16 * R₀ ≤ R) (hs : 1 ≤ s) (hC : 0 ≤ C)
    (hX : 1 + (R : ℝ) * (s : ℝ) ^ 2 * n ≤ X)
    (f : ↥(initialReferenceRows (R₀ * n)) → ℝ)
    (hf : ∀ j, f j ≤ C * X ^ p) :
    ∑ j, f j ≤ (10 * C) * X ^ (p + 1) :=
  sum_le_initialReferenceRows_polynomial (R₀ * n) p (by positivity) hC
    (initialReferenceRows_card_le_charge hR hs) hX f hf

/-- In particular, the degree-ten per-cell remainder becomes degree eleven
after summing every initial row. -/
theorem sum_le_initialReferenceRows_degree_eleven
    {R₀ R s n : ℕ} {C X : ℝ}
    (hR : 16 * R₀ ≤ R) (hs : 1 ≤ s) (hC : 0 ≤ C)
    (hX : 1 + (R : ℝ) * (s : ℝ) ^ 2 * n ≤ X)
    (f : ↥(initialReferenceRows (R₀ * n)) → ℝ)
    (hf : ∀ j, f j ≤ C * X ^ 10) :
    ∑ j, f j ≤ (10 * C) * X ^ 11 :=
  sum_le_initialReferenceRows_polynomial_charge 10 hR hs hC hX f hf

end GapFamily.Construction
