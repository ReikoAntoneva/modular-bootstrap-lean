import GapFamily.Analytic.Arithmetic.SelbergUnit

/-!
# Reality of the finite Kloosterman sum

Negation on the finite unit group pairs each phase with its complex conjugate.
The sum is therefore fixed by conjugation, including at denominator one.
-/

noncomputable section

namespace GapFamily.Analytic

/-- Conjugation of a phase negates the summation unit. -/
theorem conj_kloostermanPhase (j J : ℤ) (n : ℕ) (d : (ZMod (n + 1))ˣ) :
    starRingEnd ℂ (kloostermanPhase j J n d) = kloostermanPhase j J n (-d) := by
  unfold kloostermanPhase
  simp only [inv_neg, Units.val_neg, mul_neg, ← neg_add]
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

/-- The actual finite Kloosterman sum is fixed by complex conjugation. -/
theorem conj_kloostermanSum (j J : ℤ) (n : ℕ) :
    starRingEnd ℂ (kloostermanSum j J n) = kloostermanSum j J n := by
  unfold kloostermanSum
  rw [map_sum]
  simp_rw [conj_kloostermanPhase]
  exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)

end GapFamily.Analytic
