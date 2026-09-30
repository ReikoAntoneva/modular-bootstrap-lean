import GapFamily.Analytic.Cusp.Scalar.CuspScalarResolvent
import GapFamily.Analytic.Foundation.CompactSelfAdjointPencilBasic

/-!
# The actual scalar cusp response pencil

The affine pencil is I−(z+1)R for the actual scalar Riesz response.
Its totalized algebra inverse gives a form-valued source family; inverse
identities are stated only at actual unit parameters.
-/

noncomputable section

namespace GapFamily.Analytic

/-- The actual scalar cusp response pencil. -/
def cuspScalarPencil (z : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  compactSelfAdjointPencil cuspScalarWeakResolvent z

@[simp] theorem cuspScalarPencil_apply (z : ℂ) (f : ModularHilbert) :
    cuspScalarPencil z f = f - (z + 1) • cuspScalarWeakResolvent f := rfl

@[simp] theorem cuspScalarPencil_neg_one : cuspScalarPencil (-1) = 1 :=
  compactSelfAdjointPencil_neg_one cuspScalarWeakResolvent

theorem cuspScalarPencil_zero : cuspScalarPencil 0 = 1 - cuspScalarWeakResolvent := by
  simp [cuspScalarPencil, compactSelfAdjointPencil]

/-- The proved quarter-energy bound makes the actual scalar pencil regular at zero. -/
theorem cuspScalarPencil_isUnit_zero : IsUnit (cuspScalarPencil 0) := by
  rw [cuspScalarPencil_zero]
  apply isUnit_one_sub_of_norm_lt_one
  exact cuspScalarWeakResolvent_norm_le.trans_lt (by norm_num)

/-- The actual scalar form-valued source family, using the algebra inverse. -/
def cuspScalarPencilSolution (z : ℂ) : ModularHilbert →L[ℂ] cuspScalarForm :=
  cuspScalarWeakSolution.comp (Ring.inverse (cuspScalarPencil z))

theorem cuspScalarPencilSolution_apply (z : ℂ) (f : ModularHilbert) :
    cuspScalarPencilSolution z f =
      cuspScalarWeakSolution (Ring.inverse (cuspScalarPencil z) f) := rfl

theorem cuspScalarPencil_apply_inverse {z : ℂ} (hz : IsUnit (cuspScalarPencil z))
    (f : ModularHilbert) :
    cuspScalarPencil z (Ring.inverse (cuspScalarPencil z) f) = f := by
  have h := congrArg (fun A : ModularHilbert →L[ℂ] ModularHilbert => A f)
    (Ring.mul_inverse_cancel (cuspScalarPencil z) hz)
  exact h

theorem cuspScalarPencil_inverse_apply {z : ℂ} (hz : IsUnit (cuspScalarPencil z))
    (f : ModularHilbert) :
    Ring.inverse (cuspScalarPencil z) (cuspScalarPencil z f) = f := by
  have h := congrArg (fun A : ModularHilbert →L[ℂ] ModularHilbert => A f)
    (Ring.inverse_mul_cancel (cuspScalarPencil z) hz)
  exact h

/-- The mass-shift parameter gives the original actual Riesz source response. -/
@[simp] theorem cuspScalarPencilSolution_neg_one :
    cuspScalarPencilSolution (-1) = cuspScalarWeakSolution := by
  apply ContinuousLinearMap.ext
  intro f
  rw [cuspScalarPencilSolution_apply, cuspScalarPencil_neg_one, Ring.inverse_one]
  rfl

end GapFamily.Analytic
