import GapFamily.Analytic.Poincare.Poincare

/-!
# Decomposition of a modular matrix over its cusp coset

The chosen representative of each left cusp coset gives a product
decomposition of the full matrix group. Both matrix signs remain in the
cusp-subgroup coordinate.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open scoped MatrixGroups

theorem cuspCoset_mk_mul_out (q : CuspCoset) (h : cuspInfinity) :
    (Quotient.mk _ ((h : SL(2, ℤ)) * q.out) : CuspCoset) = q := by
  calc
    _ = Quotient.mk _ q.out := Quotient.sound (by
      change QuotientGroup.rightRel cuspInfinity ((h : SL(2, ℤ)) * q.out) q.out
      rw [QuotientGroup.rightRel_apply]
      simpa [_root_.mul_inv_rev] using cuspInfinity.inv_mem h.property)
    _ = q := Quotient.out_eq q

/-- A modular matrix is uniquely a cusp matrix times its chosen coset representative. -/
def cuspMatrixEquiv : CuspCoset × cuspInfinity ≃ SL(2, ℤ) :=
  Equiv.ofBijective (fun p => (p.2 : SL(2, ℤ)) * p.1.out) (by
    constructor
    · rintro ⟨q, h⟩ ⟨q', h'⟩ heq
      change (h : SL(2, ℤ)) * q.out = (h' : SL(2, ℤ)) * q'.out at heq
      have hq : q = q' := by
        rw [← cuspCoset_mk_mul_out q h, heq, cuspCoset_mk_mul_out q' h']
      subst q'
      have hh : h = h' := Subtype.ext (mul_right_cancel heq)
      subst h'
      rfl
    · intro g
      let q : CuspCoset := Quotient.mk _ g
      have hm : g * q.out⁻¹ ∈ cuspInfinity := by
        exact QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq q))
      refine ⟨(q, ⟨g * q.out⁻¹, hm⟩), ?_⟩
      simp)

@[simp] theorem cuspMatrixEquiv_apply (q : CuspCoset) (h : cuspInfinity) :
    cuspMatrixEquiv (q, h) = (h : SL(2, ℤ)) * q.out := rfl

end GapFamily.Analytic.SpatialPoint
