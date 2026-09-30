import GapFamily.Analytic.Foundation.LatticeEisenstein

/-! Actual spin-dependent seeds on both signs of primitive integer rows. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourier
open Set UpperHalfPlane
open scoped MatrixGroups

/-- A genuine determinant-one representative with the prescribed primitive row. -/
def primitiveMatrix (v : PrimitiveRow) : SL(2, ℤ) :=
  Classical.choose (primitiveRow_has_representative v.val
    ((EisensteinSeries.mem_gammaSet_one _).mp v.property))

theorem primitiveMatrix_bottomRow (v : PrimitiveRow) : (primitiveMatrix v) 1 = v.val :=
  Classical.choose_spec (primitiveRow_has_representative v.val
    ((EisensteinSeries.mem_gammaSet_one _).mp v.property))

/-- This is the literal seed at the chosen primitive-row matrix, including its phase. -/
def primitiveSpinTerm (J : ℤ) (s : ℂ) (z : UpperHalfPlane) (v : PrimitiveRow) : ℂ :=
  complexPointSeed 0 J s (primitiveMatrix v • z)

/-- Both signs of a primitive row give the same actual spin-dependent quotient term. -/
theorem primitiveSpinTerm_signed (J : ℤ) (s : ℂ) (z : UpperHalfPlane)
    (q : CuspCoset) (b : Bool) :
    primitiveSpinTerm J s z (cuspSignedRowEquiv (q, b)) =
      complexPoincareTerm 0 J s z q := by
  have hr : QuotientGroup.rightRel cuspInfinity
      (primitiveMatrix (cuspSignedRowEquiv (q, b))) q.out := by
    apply (cuspRel_iff_bottomRow _ _).mpr
    have hrow := primitiveMatrix_bottomRow (cuspSignedRowEquiv (q, b))
    cases b
    · right
      simpa only [cuspSignedRowEquiv, Equiv.ofBijective, Equiv.coe_fn_mk,
        signedCuspBottomRow, Bool.false_eq_true, ↓reduceIte, cuspBottomRow] using hrow
    · left
      simpa only [cuspSignedRowEquiv, Equiv.ofBijective, Equiv.coe_fn_mk,
        signedCuspBottomRow, ↓reduceIte, cuspBottomRow] using hrow
  rw [primitiveSpinTerm, complexPoincareTerm_out]
  exact complexPointSeed_coset_eq 0 J s z hr

/-- Summability on the actual primitive-row index set includes both signs. -/
theorem summable_norm_primitiveSpinTerm (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (z : UpperHalfPlane) : Summable (fun v : PrimitiveRow => ‖primitiveSpinTerm J s z v‖) := by
  apply cuspSignedRowEquiv.summable_iff.mp
  have h : Summable (fun p : CuspCoset × Bool => ‖complexPoincareTerm 0 J s z p.1‖) := by
    apply (summable_prod_of_nonneg (fun p : CuspCoset × Bool => norm_nonneg
      (complexPoincareTerm 0 J s z p.1))).mpr
    refine ⟨fun q => by apply summable_of_hasFiniteSupport; exact Set.toFinite _, ?_⟩
    simpa only [tsum_bool, ← two_mul] using
      (summable_norm_complexPoincareTerm 0 J hs z).mul_left 2
  exact h.congr (fun ⟨q, b⟩ => congrArg norm (primitiveSpinTerm_signed J s z q b).symm)

/-- The literal spin-dependent primitive-row sum counts each cusp coset twice. -/
theorem primitiveSpinTerm_sum_eq_two (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (z : UpperHalfPlane) :
    (∑' v : PrimitiveRow, primitiveSpinTerm J s z v) =
      2 * complexPoincareSeries 0 J s z := by
  have hsum := (summable_norm_primitiveSpinTerm J hs z).of_norm
  rw [← cuspSignedRowEquiv.tsum_eq]
  have hp := cuspSignedRowEquiv.summable_iff.mpr hsum
  simp only [Function.comp_def] at hp
  rw [hp.tsum_prod]
  simp_rw [primitiveSpinTerm_signed, tsum_bool, ← two_mul]
  exact tsum_mul_left

/-- The convergent actual Poincaré series is one half of the signed primitive-row series. -/
theorem hasSum_half_primitiveSpinTerm (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (z : UpperHalfPlane) :
    HasSum (fun v : PrimitiveRow => (1 / 2 : ℂ) * primitiveSpinTerm J s z v)
      (complexPoincareSeries 0 J s z) := by
  have h := (summable_norm_primitiveSpinTerm J hs z).of_norm.hasSum.mul_left (1 / 2 : ℂ)
  rw [primitiveSpinTerm_sum_eq_two J hs z] at h
  simpa only [← mul_assoc, one_div_mul_cancel (by norm_num : (2 : ℂ) ≠ 0), one_mul] using h

end GapFamily.Analytic.PoincareFourier
