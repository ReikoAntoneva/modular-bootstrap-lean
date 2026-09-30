import GapFamily.Construction.TailErrorBudget

/-! Integer moment counts at real charge, with uniform degree and repair reserves. -/

noncomputable section
open Real
namespace GapFamily.Construction

/-- A natural moment degree at an arbitrary real charge. -/
def realTailMomentDegree (K : ℕ) (a : ℝ) (m : ℕ) : ℕ :=
  tailMomentDegree K ⌈a⌉₊ m

@[simp] theorem realTailMomentDegree_cast (K : ℕ) (a : ℝ) (m : ℕ) :
    (realTailMomentDegree K a m : ℝ) =
      (K : ℝ) * ((⌈a⌉₊ : ℝ) + m + 1) := by
  simp [realTailMomentDegree]

theorem realTailMomentDegree_pos {K m : ℕ} (hK : 0 < K) (a : ℝ) :
    1 ≤ realTailMomentDegree K a m := by
  unfold realTailMomentDegree tailMomentDegree
  exact Nat.succ_le_iff.mpr (Nat.mul_pos hK (by omega))

/-- The degree controls the charge plus every endpoint in its integer layer. -/
theorem realTailMomentDegree_lower {K m : ℕ} {a L : ℝ}
    (hL : L < (m : ℝ) + 1) :
    (K : ℝ) * (a + L) ≤ (realTailMomentDegree K a m : ℝ) := by
  rw [realTailMomentDegree_cast]
  exact mul_le_mul_of_nonneg_left (by linarith [Nat.le_ceil a]) (Nat.cast_nonneg K)

/-- The rounded degree still has a linear upper bound uniform in the layer. -/
theorem realTailMomentDegree_add_one_le {K m : ℕ} {a L : ℝ}
    (ha : 1 ≤ a) (hm : (m : ℝ) ≤ L) :
    (realTailMomentDegree K a m : ℝ) + 1 ≤
      (3 * ((K : ℝ) + 1)) * (a + L) := by
  rw [realTailMomentDegree_cast]
  have hc := Nat.ceil_lt_add_one (show 0 ≤ a by linarith)
  have hL : 0 ≤ L := (Nat.cast_nonneg m).trans hm
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hprod := mul_le_mul_of_nonneg_left
    (show (⌈a⌉₊ : ℝ) + m + 1 ≤ 3 * (a + L) by linarith) hK
  nlinarith

/-- Rounding the charge upward only strengthens the moment reserve. -/
theorem realTailMomentDegree_error_le_slotBudget {C : ℝ} {K : ℕ}
    (hK : C + 16 ≤ (K : ℝ) * log 2) (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    exp (C * (a + m + 1) - (realTailMomentDegree K a m : ℝ) * log 2) ≤
      Layer.slotBudget m := by
  apply le_trans (b := exp (-16 * (a + m + 1)))
  · apply exp_le_exp.mpr
    rw [realTailMomentDegree_cast]
    have hreserve := mul_le_mul_of_nonneg_right hK
      (by positivity : 0 ≤ a + m + 1)
    have hround := mul_le_mul_of_nonneg_left (Nat.le_ceil a)
      (mul_nonneg (Nat.cast_nonneg K) (log_pos (by norm_num : (1 : ℝ) < 2)).le)
    nlinarith
  · exact exp_neg_sixteen_le_slotBudget a ha m

end GapFamily.Construction
