import GapFamily.Analytic.Poincare.PoincarePositiveRow

/-! Actual nonidentity cusp cosets have exactly one primitive lower row of positive first entry. -/

noncomputable section
namespace GapFamily.Analytic.PoincareFourierRegroup

open PoincareFourier PoincareFourierUnfold
open scoped MatrixGroups

/-- The actual cusp coset of the determinant-one representative of a positive primitive row. -/
def positiveRowCoset (v : {v : PrimitiveRow // 0 < v.val 0}) :
    {q : CuspCoset // q ≠ identityCuspCoset} :=
  ⟨Quotient.mk _ (primitiveMatrix v.val), by
    intro h
    change Quotient.mk _ (primitiveMatrix v.val) = Quotient.mk _ (1 : SL(2, ℤ)) at h
    have hc : primitiveMatrix v.val 1 0 ≠ 0 := by
      rw [primitiveMatrix_bottomRow]
      exact v.property.ne'
    rcases (cuspRel_iff_bottomRow (primitiveMatrix v.val) 1).mp
      (Quotient.exact h) with hrow | hrow
    · exact hc (by simpa using congrFun hrow 0)
    · exact hc (by simpa using congrFun hrow 0)⟩

@[simp] theorem positiveRowCoset_val (v : {v : PrimitiveRow // 0 < v.val 0}) :
    (positiveRowCoset v).val = Quotient.mk _ (primitiveMatrix v.val) := rfl

theorem positiveRowCoset_injective : Function.Injective positiveRowCoset := by
  intro v w h
  have hq : Quotient.mk _ (primitiveMatrix v.val) =
      Quotient.mk _ (primitiveMatrix w.val) := congrArg Subtype.val h
  have hrow := (cuspRel_iff_bottomRow (primitiveMatrix v.val) (primitiveMatrix w.val)).mp
    (Quotient.exact hq)
  rw [primitiveMatrix_bottomRow, primitiveMatrix_bottomRow] at hrow
  rcases hrow with hrow | hrow
  · exact Subtype.ext (Subtype.ext hrow)
  · have h0 := congrFun hrow 0
    simp only [Pi.neg_apply] at h0
    have hv := v.property
    have hw := w.property
    omega

/-- Vanishing first lower entry characterizes membership in the identity cusp coset. -/
theorem cuspBottomRow_zero_implies_identity {q : CuspCoset}
    (hc : cuspBottomRow q 0 = 0) : q = identityCuspCoset := by
  have hmem : q.out ∈ cuspInfinity := hc
  have hrel : QuotientGroup.rightRel cuspInfinity q.out (1 : SL(2, ℤ)) := by
    rw [QuotientGroup.rightRel_apply]
    simpa using cuspInfinity.inv_mem hmem
  exact q.out_eq.symm.trans (Quotient.sound hrel)

theorem positiveRowCoset_surjective : Function.Surjective positiveRowCoset := by
  intro q
  have hc : cuspBottomRow q.val 0 ≠ 0 := by
    intro h
    exact q.property (cuspBottomRow_zero_implies_identity h)
  have hv : ∃ v : PrimitiveRow, 0 < v.val 0 ∧
      (v.val = cuspBottomRow q.val ∨ v.val = -cuspBottomRow q.val) := by
    by_cases hpos : 0 < cuspBottomRow q.val 0
    · refine ⟨signedCuspBottomRow (q.val, true), ?_, Or.inl rfl⟩
      simpa [signedCuspBottomRow] using hpos
    · refine ⟨signedCuspBottomRow (q.val, false), ?_, Or.inr rfl⟩
      change 0 < -cuspBottomRow q.val 0
      omega
  obtain ⟨v, hpos, hrow⟩ := hv
  refine ⟨⟨v, hpos⟩, Subtype.ext ?_⟩
  change Quotient.mk _ (primitiveMatrix v) = q.val
  rw [← q.val.out_eq]
  apply Quotient.sound
  apply (cuspRel_iff_bottomRow (primitiveMatrix v) q.val.out).mpr
  simpa only [primitiveMatrix_bottomRow, cuspBottomRow] using hrow

/-- A genuine bijection with positive primitive rows, removing the simultaneous-sign ambiguity. -/
def positiveRowCosetEquiv : {v : PrimitiveRow // 0 < v.val 0} ≃
    {q : CuspCoset // q ≠ identityCuspCoset} :=
  Equiv.ofBijective positiveRowCoset
    ⟨positiveRowCoset_injective, positiveRowCoset_surjective⟩

@[simp] theorem positiveRowCosetEquiv_apply_val (v : {v : PrimitiveRow // 0 < v.val 0}) :
    (positiveRowCosetEquiv v).val = Quotient.mk _ (primitiveMatrix v.val) := rfl

/-- Actual nonidentity cusp cosets indexed once by a positive modulus,
unit residue, and unrestricted integer translate. -/
def nonidentityResidueEquiv : {q : CuspCoset // q ≠ identityCuspCoset} ≃
    (Σ n : ℕ, (ZMod (n + 1))ˣ × ℤ) :=
  positiveRowCosetEquiv.symm.trans positiveResidueRowEquiv.symm

/-- The inverse is the literal quotient of the previously constructed residue-row matrix. -/
@[simp] theorem nonidentityResidueEquiv_symm_apply_val
    (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) :
    (nonidentityResidueEquiv.symm ⟨n, (u, k)⟩).val =
      Quotient.mk _ (primitiveMatrix (residueRow n u k)) := rfl

end GapFamily.Analytic.PoincareFourierRegroup
