import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Constructing an unbounded self-adjoint inverse shift

This realizes `T⁻¹ - I` on the actual range of a bounded injective symmetric
operator. Dense range supplies the adjoint-domain argument. No unbounded
operator, self-adjoint extension, or resolvent is assumed.
-/

noncomputable section

namespace GapFamily.Analytic.Dirichlet

open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The unbounded inverse of an injective bounded map, shifted by the identity.
Its domain is the actual range of the bounded map. -/
def inverseShift (T : H →L[𝕜] H) (hT : Function.Injective T) : H →ₗ.[𝕜] H where
  domain := T.range
  toFun := (LinearEquiv.ofInjective T.toLinearMap hT).symm.toLinearMap - T.range.subtype

@[simp]
theorem inverseShift_domain (T : H →L[𝕜] H) (hT : Function.Injective T) :
    (inverseShift T hT).domain = T.range := rfl

theorem inverseShift_apply (T : H →L[𝕜] H) (hT : Function.Injective T)
    (x : (inverseShift T hT).domain) :
    inverseShift T hT x = (LinearEquiv.ofInjective T.toLinearMap hT).symm x - x := rfl

@[simp]
theorem inverseShift_apply_range (T : H →L[𝕜] H) (hT : Function.Injective T) (x : H) :
    inverseShift T hT ⟨T x, LinearMap.mem_range_self T.toLinearMap x⟩ = x - T x := by
  change (LinearEquiv.ofInjective T.toLinearMap hT).symm
    ((LinearEquiv.ofInjective T.toLinearMap hT) x) - T x = _
  rw [LinearEquiv.symm_apply_apply]

theorem inverseShift_apply_range_add (T : H →L[𝕜] H) (hT : Function.Injective T) (x : H) :
    inverseShift T hT ⟨T x, LinearMap.mem_range_self T.toLinearMap x⟩ + T x = x := by
  rw [inverseShift_apply_range, sub_add_cancel]

theorem inverseShift_image_apply_add (T : H →L[𝕜] H) (hT : Function.Injective T)
    (x : (inverseShift T hT).domain) : T (inverseShift T hT x + x) = x := by
  rw [inverseShift_apply, sub_add_cancel]
  exact LinearEquiv.ofInjective_symm_apply T.toLinearMap x

variable [CompleteSpace H]

theorem inverseShift_isFormalAdjoint (T : H →L[𝕜] H) (hT : Function.Injective T)
    (hsa : IsSelfAdjoint T) : (inverseShift T hT).IsFormalAdjoint (inverseShift T hT) := by
  intro x y
  let E := LinearEquiv.ofInjective T.toLinearMap hT
  have hx : T (E.symm x) = x := LinearEquiv.ofInjective_symm_apply T.toLinearMap x
  have hy : T (E.symm y) = y := LinearEquiv.ofInjective_symm_apply T.toLinearMap y
  change ⟪E.symm x - x, (y : H)⟫_𝕜 = ⟪(x : H), E.symm y - y⟫_𝕜
  rw [inner_sub_left, inner_sub_right]
  congr 1
  rw [← hx, ← hy]
  exact (hsa.isSymmetric (E.symm x) (E.symm y)).symm

theorem inverseShift_isSelfAdjoint (T : H →L[𝕜] H) (hT : Function.Injective T)
    (hdense : DenseRange T) (hs : T.toLinearMap.IsSymmetric) :
    IsSelfAdjoint (inverseShift T hT) := by
  have hsa : IsSelfAdjoint T := hs.isSelfAdjoint
  let A := inverseShift T hT
  have hd : Dense (A.domain : Set H) := hdense
  have hsym : A.IsFormalAdjoint A := inverseShift_isFormalAdjoint T hT hsa
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ (hsym.le_adjoint hd)
  apply LinearPMap.le_of_eqLocus_ge
  intro u hu
  let U : A.adjoint.domain := ⟨u, hu⟩
  have hTu : T (A.adjoint U + u) = u := by
    apply ext_inner_right 𝕜
    intro x
    have hp := LinearPMap.adjoint_isFormalAdjoint hd U
      ⟨T x, LinearMap.mem_range_self T.toLinearMap x⟩
    change ⟪A.adjoint U, T x⟫_𝕜 = ⟪u, A ⟨T x, _⟩⟫_𝕜 at hp
    rw [show A ⟨T x, _⟩ = x - T x from inverseShift_apply_range T hT x,
      inner_sub_right] at hp
    calc
      ⟪T (A.adjoint U + u), x⟫_𝕜 = ⟪A.adjoint U + u, T x⟫_𝕜 :=
        hsa.isSymmetric _ _
      _ = ⟪A.adjoint U, T x⟫_𝕜 + ⟪u, T x⟫_𝕜 := inner_add_left _ _ _
      _ = ⟪u, x⟫_𝕜 := by rw [hp, sub_add_cancel]
  have huA : u ∈ A.domain := ⟨A.adjoint U + u, hTu⟩
  refine ⟨hu, huA, ?_⟩
  apply hT
  have hh := inverseShift_image_apply_add T hT (⟨u, huA⟩ : A.domain)
  change T (A ⟨u, huA⟩ + u) = u at hh
  have he : T (A.adjoint U + u) = T (A ⟨u, huA⟩ + u) := hTu.trans hh.symm
  simpa only [map_add, add_left_inj] using he

theorem inverseShift_isClosed (T : H →L[𝕜] H) (hT : Function.Injective T)
    (hdense : DenseRange T) (hs : T.toLinearMap.IsSymmetric) : (inverseShift T hT).IsClosed :=
  (inverseShift_isSelfAdjoint T hT hdense hs).isClosed

end GapFamily.Analytic.Dirichlet
