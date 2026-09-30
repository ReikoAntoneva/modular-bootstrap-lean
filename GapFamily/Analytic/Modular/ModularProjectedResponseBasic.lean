import GapFamily.Analytic.Modular.ModularResolvent
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The actual mean-zero projected modular response

The constant-orthogonal projection commutes with the genuine shifted weak
resolvent. Their composition equals a positive orthogonal compression, hence
is positive and self-adjoint on the actual ambient modular Hilbert space.
-/

noncomputable section
namespace GapFamily.Analytic.ModularProjected

open ModularGradient

def projectedWeakResolvent : ModularHilbert →L[ℂ] ModularHilbert :=
  modularMeanZeroProjection.comp weakResolvent

@[simp] theorem projectedWeakResolvent_apply (f : ModularHilbert) :
    projectedWeakResolvent f = modularMeanZeroProjection (weakResolvent f) := rfl

theorem projectedWeakResolvent_eq_resolvent_projection (f : ModularHilbert) :
    projectedWeakResolvent f = weakResolvent (modularMeanZeroProjection f) :=
  (weakResolvent_meanZeroProjection f).symm

theorem projectedWeakResolvent_eq_comp_projection :
    projectedWeakResolvent = weakResolvent.comp modularMeanZeroProjection := by
  apply ContinuousLinearMap.ext
  intro f
  exact projectedWeakResolvent_eq_resolvent_projection f

theorem projectedWeakResolvent_mem_meanZero (f : ModularHilbert) :
    projectedWeakResolvent f ∈ modularMeanZero :=
  modularMeanZero.starProjection_apply_mem (weakResolvent f)

@[simp] theorem projectedWeakResolvent_projection (f : ModularHilbert) :
    projectedWeakResolvent (modularMeanZeroProjection f) = projectedWeakResolvent f := by
  rw [projectedWeakResolvent_apply, weakResolvent_meanZeroProjection]
  exact modularMeanZero.starProjection_eq_self_iff.mpr
    (modularMeanZero.starProjection_apply_mem (weakResolvent f))

theorem projectedWeakResolvent_isPositive : projectedWeakResolvent.IsPositive := by
  have hpos := ContinuousLinearMap.IsPositive.conj_starProjection modularMeanZero
    weakResolvent_isPositive
  have heq : (modularMeanZero.starProjection.comp weakResolvent).comp
      modularMeanZero.starProjection = projectedWeakResolvent := by
    apply ContinuousLinearMap.ext
    intro f
    exact projectedWeakResolvent_projection f
  rw [← heq]
  exact hpos

theorem projectedWeakResolvent_isSelfAdjoint : IsSelfAdjoint projectedWeakResolvent :=
  projectedWeakResolvent_isPositive.isSelfAdjoint

@[simp] theorem projectedWeakResolvent_constant : projectedWeakResolvent modularConstant = 0 := by
  rw [projectedWeakResolvent_apply, weakResolvent_constant, modularMeanZeroProjection_eq,
    sub_apply, ContinuousLinearMap.id_apply,
    modularConstantProjection_apply, modularAverage_constant, one_smul, sub_self]

theorem projectedWeakResolvent_eq_weakResolvent_of_mem {f : ModularHilbert}
    (hf : f ∈ modularMeanZero) : projectedWeakResolvent f = weakResolvent f := by
  rw [projectedWeakResolvent_eq_resolvent_projection]
  congr 1
  exact modularMeanZero.starProjection_eq_self_iff.mpr hf

theorem projectedWeakResolvent_eq_sub_constantProjection (f : ModularHilbert) :
    projectedWeakResolvent f = weakResolvent f - modularConstantProjection f := by
  rw [projectedWeakResolvent_apply, modularMeanZeroProjection_eq,
    sub_apply, ContinuousLinearMap.id_apply,
    constantProjection_weakResolvent]

end GapFamily.Analytic.ModularProjected
