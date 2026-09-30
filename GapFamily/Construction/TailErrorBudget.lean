import GapFamily.Construction.CellScheduleDegree
import GapFamily.Layer

/-! A single integer moment multiplier pays every slot budget, uniformly over
all later layers. Its choice depends only on the fixed analytic exponent loss,
and therefore precedes the final charge ratio. -/

noncomputable section
namespace GapFamily.Construction

private theorem slotBudget_denominator_le_exp (m : ℕ) :
    512 * (2 * (m : ℝ) + 1) * (m + 1) * (m + 2) ≤
      Real.exp (16 * ((m : ℝ) + 1)) := by
  have h512 : (512 : ℝ) ≤ Real.exp 9 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 9
    norm_num [← Real.exp_nat_mul] at hpow ⊢
    exact hpow
  have h1 : 2 * (m : ℝ) + 1 ≤ Real.exp (2 * m) := Real.add_one_le_exp _
  have h2 : (m : ℝ) + 1 ≤ Real.exp m := Real.add_one_le_exp _
  have h3 : (m : ℝ) + 2 ≤ Real.exp ((m : ℝ) + 1) := by
    simpa only [add_assoc, one_add_one_eq_two] using Real.add_one_le_exp ((m : ℝ) + 1)
  calc
    _ ≤ Real.exp 9 * Real.exp (2 * m) * Real.exp m * Real.exp ((m : ℝ) + 1) :=
      mul_le_mul (mul_le_mul (mul_le_mul h512 h1 (by positivity) (by positivity))
        h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
    _ = Real.exp (9 + 2 * m + m + ((m : ℝ) + 1)) := by simp only [Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) m; linarith)

/-- An exponential reserve of sixteen per charge-and-layer unit is enough for
the literal rational slot allowance, including the first layer. -/
theorem exp_neg_sixteen_le_slotBudget (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    Real.exp (-16 * (a + m + 1)) ≤ Layer.slotBudget m := by
  have hden := (slotBudget_denominator_le_exp m).trans
    (Real.exp_le_exp.mpr (by linarith : 16 * ((m : ℝ) + 1) ≤ 16 * (a + m + 1)))
  rw [show -16 * (a + m + 1) = -(16 * (a + m + 1)) by ring, Real.exp_neg]
  simpa only [one_div, Layer.slotBudget] using
    one_div_le_one_div_of_le (by positivity) hden

/-- A moment degree paying the fixed analytic loss plus sixteen controls every
slot. The degree is exactly the natural frozen schedule, without rounding. -/
theorem tailMomentDegree_error_le_slotBudget {C : ℝ} {K : ℕ}
    (hK : C + 16 ≤ (K : ℝ) * Real.log 2) (a m : ℕ) :
    Real.exp (C * ((a : ℝ) + m + 1) -
      (tailMomentDegree K a m : ℝ) * Real.log 2) ≤ Layer.slotBudget m := by
  apply le_trans (b := Real.exp (-16 * ((a : ℝ) + m + 1)))
  · apply Real.exp_le_exp.mpr
    rw [tailMomentDegree_cast]
    have h := mul_le_mul_of_nonneg_right hK
      (by positivity : 0 ≤ (a : ℝ) + m + 1)
    nlinarith
  · exact exp_neg_sixteen_le_slotBudget _ (Nat.cast_nonneg _) _

/-- The tail multiplier is selected from fixed analytic constants alone, before
the scale ratio and the lower cutoff are chosen. -/
theorem exists_tailMomentMultiplier (C : ℝ) :
    ∃ K : ℕ, 0 < K ∧ C + 16 ≤ (K : ℝ) * Real.log 2 ∧
      ∀ a m : ℕ, Real.exp (C * ((a : ℝ) + m + 1) -
        (tailMomentDegree K a m : ℝ) * Real.log 2) ≤ Layer.slotBudget m := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max 0 ((C + 16) / Real.log 2))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : 0 < K := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hK)
  have hbound : C + 16 ≤ (K : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog).mp ((le_max_right _ _).trans hK.le)
  exact ⟨K, hpos, hbound, tailMomentDegree_error_le_slotBudget hbound⟩

end GapFamily.Construction
