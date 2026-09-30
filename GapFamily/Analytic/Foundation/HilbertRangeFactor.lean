import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Bounded factorization through a Hilbert range

Norm domination makes the map well defined on the actual range. Its continuous
extension to the closed range is composed with the Hilbert orthogonal projection.
-/

noncomputable section
namespace GapFamily.Analytic

open Set

variable {V E G : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem exists_hilbert_factor_of_norm_bound
    (T : V →L[ℂ] G) (R : V →L[ℂ] E)
    (h : ∃ C : ℝ, ∀ x, ‖T x‖ ≤ C * ‖R x‖) :
    ∃ B : E →L[ℂ] G, B.comp R = T := by
  let S : Submodule ℂ E := R.range
  let K : Submodule ℂ E := S.topologicalClosure
  let e : S →L[ℂ] K := S.subtypeL.codRestrict K (fun x => S.le_topologicalClosure x.property)
  have he_dense : DenseRange e :=
    (denseRange_inclusion_iff S.le_topologicalClosure).2 (by rfl)
  have he_uniform : IsUniformInducing e :=
    (isUniformEmbedding_set_inclusion S.le_topologicalClosure).isUniformInducing
  let t : S →L[ℂ] G := T.toLinearMap.compLeftInverse R.toLinearMap
  let t' : K →L[ℂ] G := t.extend e
  refine ⟨t'.comp K.orthogonalProjectionOnto, ?_⟩
  ext x
  have hRx : R x ∈ K := S.le_topologicalClosure (R.mem_range_self x)
  change t' (K.orthogonalProjectionOnto (R x)) = T x
  have hp : K.orthogonalProjectionOnto (R x) = e ⟨R x, R.mem_range_self x⟩ := by
    exact K.orthogonalProjectionOnto_mem_subspace_eq_self (⟨R x, hRx⟩ : K)
  rw [hp]
  exact (t.extend_eq he_dense he_uniform ⟨R x, R.mem_range_self x⟩).trans
    (LinearMap.compLeftInverse_apply_of_bdd _ _ h x (R x) rfl)

end GapFamily.Analytic
