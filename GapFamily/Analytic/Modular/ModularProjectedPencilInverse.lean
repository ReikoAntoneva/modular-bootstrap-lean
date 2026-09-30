import GapFamily.Analytic.Modular.ModularProjectedResponse

/-!
# Actual projected pencil inverse identity

The projected response has zero constant coordinate and commutes with its
affine pencil. The algebra inverse identities are used only under the actual
unit hypothesis, which also yields commutation with the inverse pencil.
-/

noncomputable section
namespace GapFamily.Analytic.ModularProjected

@[simp] theorem projectedPencil_apply (z : ℂ) (f : ModularHilbert) :
    projectedPencil z f = f - (z + 1) • projectedWeakResolvent f := rfl

theorem projectedPencil_apply_inverse {z : ℂ} (hQ : IsUnit (projectedPencil z))
    (f : ModularHilbert) :
    projectedPencil z (Ring.inverse (projectedPencil z) f) = f := by
  have h := congrArg (fun A : ModularHilbert →L[ℂ] ModularHilbert => A f)
    (Ring.mul_inverse_cancel (projectedPencil z) hQ)
  exact h

theorem projectedPencil_inverse_apply {z : ℂ} (hQ : IsUnit (projectedPencil z))
    (f : ModularHilbert) :
    Ring.inverse (projectedPencil z) (projectedPencil z f) = f := by
  have h := congrArg (fun A : ModularHilbert →L[ℂ] ModularHilbert => A f)
    (Ring.inverse_mul_cancel (projectedPencil z) hQ)
  exact h

@[simp] theorem constantProjection_projectedWeakResolvent (f : ModularHilbert) :
    modularConstantProjection (projectedWeakResolvent f) = 0 :=
  (modularConstantProjection_eq_zero_iff _).mpr
    ((mem_modularMeanZero_iff _).mp (projectedWeakResolvent_mem_meanZero f))

@[simp] theorem constantProjection_projectedPencil (z : ℂ) (f : ModularHilbert) :
    modularConstantProjection (projectedPencil z f) = modularConstantProjection f := by
  rw [projectedPencil_apply, map_sub, map_smul,
    constantProjection_projectedWeakResolvent, smul_zero, sub_zero]

theorem constantProjection_pencil_inverse {z : ℂ} (hQ : IsUnit (projectedPencil z))
    (f : ModularHilbert) :
    modularConstantProjection (Ring.inverse (projectedPencil z) f) =
      modularConstantProjection f := by
  have h := congrArg modularConstantProjection (projectedPencil_apply_inverse hQ f)
  simpa only [constantProjection_projectedPencil] using h

theorem projectedPencil_commutes_response (z : ℂ) (f : ModularHilbert) :
    projectedPencil z (projectedWeakResolvent f) =
      projectedWeakResolvent (projectedPencil z f) := by
  simp only [projectedPencil_apply, map_sub, map_smul]

theorem projected_response_inverse_commute {z : ℂ} (hQ : IsUnit (projectedPencil z))
    (f : ModularHilbert) :
    projectedWeakResolvent (Ring.inverse (projectedPencil z) f) =
      Ring.inverse (projectedPencil z) (projectedWeakResolvent f) := by
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hQ).1
  rw [projectedPencil_commutes_response, projectedPencil_apply_inverse hQ,
    projectedPencil_apply_inverse hQ]

end GapFamily.Analytic.ModularProjected
