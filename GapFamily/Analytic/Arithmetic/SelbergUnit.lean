import GapFamily.Analytic.Arithmetic.Kloosterman

/-!
# Unit changes of variable for the finite Kloosterman sum

These identities use inversion and multiplication on the actual finite unit
group. They apply also to the denominator one.
-/

noncomputable section

namespace GapFamily.Analytic

/-- Inversion of the summation unit exchanges the two arithmetic frequencies. -/
theorem kloostermanPhase_inv (j J : ℤ) (n : ℕ) (d : (ZMod (n + 1))ˣ) :
    kloostermanPhase j J n d⁻¹ = kloostermanPhase J j n d := by
  simp [kloostermanPhase, add_comm]

/-- The finite Kloosterman sum is symmetric in its two frequencies. -/
theorem kloostermanSum_symm (j J : ℤ) (n : ℕ) :
    kloostermanSum j J n = kloostermanSum J j n := by
  unfold kloostermanSum
  apply Fintype.sum_equiv (Equiv.inv _) _ _
  intro d
  simpa only [Equiv.inv_apply] using (kloostermanPhase_inv J j n d).symm

/-- Multiplication by a unit transfers an integer factor between frequencies. -/
theorem kloostermanPhase_mul_unit (j J a : ℤ) (n : ℕ)
    (u : (ZMod (n + 1))ˣ) (hu : (u : ZMod (n + 1)) = (a : ZMod (n + 1)))
    (d : (ZMod (n + 1))ˣ) :
    kloostermanPhase (a * j) J n d = kloostermanPhase j (a * J) n (u * d) := by
  unfold kloostermanPhase
  apply congrArg (fun z : ZMod (n + 1) => (ZMod.stdAddChar z : ℂ))
  simp only [Int.cast_mul, Units.val_mul, mul_inv_rev]
  rw [← hu]
  calc
    (u : ZMod (n + 1)) * j * (d : ZMod (n + 1)) +
        J * ((d⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) =
      j * ((u : ZMod (n + 1)) * (d : ZMod (n + 1))) +
        J * ((d⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) *
          ((u : ZMod (n + 1)) * ((u⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1))) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
    _ = _ := by ring

/-- Unit rescaling for the actual sum, obtained by a finite bijective reindexing. -/
theorem kloostermanSum_mul_unit (j J a : ℤ) (n : ℕ)
    (u : (ZMod (n + 1))ˣ) (hu : (u : ZMod (n + 1)) = (a : ZMod (n + 1))) :
    kloostermanSum (a * j) J n = kloostermanSum j (a * J) n := by
  unfold kloostermanSum
  exact Fintype.sum_equiv (Equiv.mulLeft u) _ _
    (kloostermanPhase_mul_unit j J a n u hu)

/-- Unit rescaling with the unit witness hidden in `IsUnit`. -/
theorem kloostermanSum_mul_of_isUnit (j J a : ℤ) (n : ℕ)
    (ha : IsUnit (a : ZMod (n + 1))) :
    kloostermanSum (a * j) J n = kloostermanSum j (a * J) n := by
  obtain ⟨u, hu⟩ := ha
  exact kloostermanSum_mul_unit j J a n u hu

/-- A unit first frequency can be normalized to one. -/
theorem kloostermanSum_eq_one_mul (j J : ℤ) (n : ℕ)
    (hj : IsUnit (j : ZMod (n + 1))) :
    kloostermanSum j J n = kloostermanSum 1 (j * J) n := by
  simpa only [mul_one] using kloostermanSum_mul_of_isUnit 1 J j n hj

end GapFamily.Analytic
