import GapFamily.Analytic.Poincare.PoincareResidueRow

/-! Positive primitive rows parametrized by a unit residue and an integer translate. -/

noncomputable section
namespace GapFamily.Analytic.PoincareFourierRegroup

open PoincareFourierUnfold PoincareFourierArithmetic

/-- The literal residue row, with its positive first coordinate retained. -/
def positiveResidueRow (p : Σ n : ℕ, (ZMod (n + 1))ˣ × ℤ) :
    {v : PrimitiveRow // 0 < v.val 0} :=
  ⟨residueRow p.1 p.2.1 p.2.2, by simp⟩

@[simp] theorem positiveResidueRow_val (p : Σ n : ℕ, (ZMod (n + 1))ˣ × ℤ) :
    (positiveResidueRow p).val = residueRow p.1 p.2.1 p.2.2 := rfl

/-- The positive first coordinate fixes the modulus, and the second fixes
the unit residue and the Euclidean quotient. -/
theorem positiveResidueRow_injective : Function.Injective positiveResidueRow := by
  rintro ⟨n, p⟩ ⟨m, q⟩ h
  have hrow : residueRow n p.1 p.2 = residueRow m q.1 q.2 :=
    congrArg Subtype.val h
  have hc := congrArg (fun v : PrimitiveRow => v.val 0) hrow
  simp only [residueRow_zero] at hc
  have hnm : n = m := by omega
  subst m
  have hd := congrArg (fun v : PrimitiveRow => v.val 1) hrow
  change ((coprimeResidueEquiv (n + 1)).symm p).val =
    ((coprimeResidueEquiv (n + 1)).symm q).val at hd
  have hpq : p = q :=
    (coprimeResidueEquiv (n + 1)).symm.injective (Subtype.ext hd)
  exact congrArg (Sigma.mk n) hpq

/-- Every positive primitive row has the actual residue and quotient coordinates. -/
theorem positiveResidueRow_surjective : Function.Surjective positiveResidueRow := by
  rintro ⟨v, hv⟩
  have hnat : ((v.val 0).toNat : ℤ) = v.val 0 := Int.toNat_of_nonneg hv.le
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v.val 0 = ((n + 1 : ℕ) : ℤ) := by
    refine ⟨(v.val 0).toNat - 1, ?_⟩
    omega
  let d : {d : ℤ // IsCoprime ((n + 1 : ℕ) : ℤ) d} := ⟨v.val 1, by
    rw [← hn]
    exact (EisensteinSeries.mem_gammaSet_one _).mp v.property⟩
  let p := coprimeResidueEquiv (n + 1) d
  refine ⟨⟨n, p⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext i
  fin_cases i
  · change ((n + 1 : ℕ) : ℤ) = v.val 0
    exact hn.symm
  · change ((coprimeResidueEquiv (n + 1)).symm
      (coprimeResidueEquiv (n + 1) d)).val = v.val 1
    rw [Equiv.symm_apply_apply]

/-- An actual equivalence with all positive primitive rows, including modulus one. -/
def positiveResidueRowEquiv : (Σ n : ℕ, (ZMod (n + 1))ˣ × ℤ) ≃
    {v : PrimitiveRow // 0 < v.val 0} :=
  Equiv.ofBijective positiveResidueRow
    ⟨positiveResidueRow_injective, positiveResidueRow_surjective⟩

@[simp] theorem positiveResidueRowEquiv_apply
    (p : Σ n : ℕ, (ZMod (n + 1))ˣ × ℤ) :
    positiveResidueRowEquiv p = positiveResidueRow p := rfl

@[simp] theorem positiveResidueRowEquiv_apply_val
    (p : Σ n : ℕ, (ZMod (n + 1))ˣ × ℤ) :
    (positiveResidueRowEquiv p).val = residueRow p.1 p.2.1 p.2.2 := rfl

end GapFamily.Analytic.PoincareFourierRegroup
