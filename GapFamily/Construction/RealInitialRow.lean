import GapFamily.Construction.InitialReferenceRepairBudgetRow

/-!
# Initial row family at a real cutoff

Rounding the nonnegative real cutoff down retains exactly the integer spins
in its closed physical window. The inherited row budget therefore applies
without restricting the cutoff to an integer.
-/

noncomputable section

open scoped BigOperators

namespace GapFamily.Construction

/-- Every integer row meeting the closed real initial spin window. -/
def realInitialRows (T : ℝ) : Finset ℤ := initialReferenceRows ⌊T⌋₊

@[simp] theorem mem_realInitialRows {T : ℝ} (hT : 0 ≤ T) (j : ℤ) :
    j ∈ realInitialRows T ↔ |(j : ℝ)| ≤ T := by
  rw [realInitialRows, mem_initialReferenceRows]
  have hcast : (j.natAbs : ℝ) = |(j : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  calc
    |(j : ℝ)| ≤ (⌊T⌋₊ : ℝ) ↔ j.natAbs ≤ ⌊T⌋₊ := by
      rw [← hcast, Nat.cast_le]
    _ ↔ (j.natAbs : ℝ) ≤ T := Nat.le_floor_iff hT
    _ ↔ |(j : ℝ)| ≤ T := by rw [hcast]

@[simp] theorem realInitialRows_natCast (T : ℕ) :
    realInitialRows (T : ℝ) = initialReferenceRows T := by
  simp [realInitialRows]

theorem realInitialRows_mono {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S) :
    realInitialRows T ⊆ realInitialRows S := by
  intro j hj
  exact (mem_realInitialRows (hT.trans hTS) j).mpr
    (((mem_realInitialRows hT j).mp hj).trans hTS)

theorem realInitialRows_card_le {T : ℝ} (hT : 0 ≤ T) :
    ((realInitialRows T).card : ℝ) ≤ 5 * (T + 1) := by
  have h := initialReferenceRows_card_le ⌊T⌋₊
  have hf := Nat.floor_le hT
  unfold realInitialRows
  linarith

theorem realInitialRows_card_le_charge {T a : ℝ} (hT : 0 ≤ T) (hTa : T ≤ a) :
    ((realInitialRows T).card : ℝ) ≤ 10 * (1 + a) := by
  have h := realInitialRows_card_le hT
  linarith

/-- The real-cutoff row count costs only one polynomial degree in a
uniform per-row remainder estimate. -/
theorem sum_le_realInitialRows_polynomial {T a C X : ℝ} (p : ℕ)
    (hT : 0 ≤ T) (hTa : T ≤ a) (hC : 0 ≤ C) (hX : 1 + a ≤ X)
    (f : ↥(realInitialRows T) → ℝ) (hf : ∀ j, f j ≤ C * X ^ p) :
    ∑ j, f j ≤ (10 * C) * X ^ (p + 1) := by
  apply initialReference_fintype_sum_prefactor p hC (by linarith) _ f hf
  simpa only [Fintype.card_coe] using
    (realInitialRows_card_le_charge hT hTa).trans
      (mul_le_mul_of_nonneg_left hX (by norm_num))

end GapFamily.Construction
