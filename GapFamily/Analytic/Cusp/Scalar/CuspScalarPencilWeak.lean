import GapFamily.Analytic.Cusp.Scalar.CuspScalarPencilBasic

/-!
# The actual scalar pencil weak equation and uniqueness

At every unit parameter the constructed response solves the scalar test-first
energy-minus-mass equation and is unique in the actual scalar form space.
Reversing inner-product arguments conjugates the spectral parameter.
-/

noncomputable section

namespace GapFamily.Analytic

/-- The actual test-first scalar weak equation has the holomorphic parameter z. -/
theorem cuspScalarPencilSolution_equation {z : ℂ}
    (hz : IsUnit (cuspScalarPencil z)) (f : ModularHilbert) (v : cuspScalarForm) :
    inner ℂ (cuspScalarGradient v) (cuspScalarGradient (cuspScalarPencilSolution z f)) -
      z * inner ℂ (scalarCuspEmbedding v)
        (scalarCuspEmbedding (cuspScalarPencilSolution z f)) =
      inner ℂ (scalarCuspEmbedding v) f := by
  let g := Ring.inverse (cuspScalarPencil z) f
  have hq : g - (z + 1) • cuspScalarWeakResolvent g = f :=
    cuspScalarPencil_apply_inverse hz f
  have hw := cuspScalarWeakSolution_equation g v
  change inner ℂ (cuspScalarGradient v) (cuspScalarGradient (cuspScalarWeakSolution g)) -
    z * inner ℂ (scalarCuspEmbedding v)
      (scalarCuspEmbedding (cuspScalarWeakSolution g)) = _
  rw [← cuspScalarWeakResolvent_apply, ← hq, inner_sub_right, inner_smul_right]
  linear_combination hw

/-- Reversing the inner-product arguments conjugates the spectral parameter. -/
theorem cuspScalarPencilSolution_equation_solution_first {z : ℂ}
    (hz : IsUnit (cuspScalarPencil z)) (f : ModularHilbert) (v : cuspScalarForm) :
    inner ℂ (cuspScalarGradient (cuspScalarPencilSolution z f)) (cuspScalarGradient v) -
      (starRingEnd ℂ z) * inner ℂ
        (scalarCuspEmbedding (cuspScalarPencilSolution z f)) (scalarCuspEmbedding v) =
      inner ℂ f (scalarCuspEmbedding v) := by
  have h := congrArg (starRingEnd ℂ) (cuspScalarPencilSolution_equation hz f v)
  simpa only [map_sub, map_mul, inner_conj_symm] using h

/-- Every actual scalar weak solution satisfies the ambient response pencil equation. -/
theorem cuspScalarPencil_apply_embedding_of_weak (z : ℂ) (f : ModularHilbert)
    (u : cuspScalarForm)
    (hu : ∀ v : cuspScalarForm,
      inner ℂ (cuspScalarGradient v) (cuspScalarGradient u) -
        z * inner ℂ (scalarCuspEmbedding v) (scalarCuspEmbedding u) =
          inner ℂ (scalarCuspEmbedding v) f) :
    cuspScalarPencil z (scalarCuspEmbedding u) = cuspScalarWeakResolvent f := by
  have huS : u = cuspScalarWeakSolution (f + (z + 1) • scalarCuspEmbedding u) := by
    apply cuspScalarWeakSolution_unique _ u
    intro v
    rw [inner_add_right, inner_smul_right]
    linear_combination hu v
  have hi := congrArg scalarCuspEmbedding huS
  change scalarCuspEmbedding u =
    cuspScalarWeakResolvent (f + (z + 1) • scalarCuspEmbedding u) at hi
  rw [map_add, map_smul] at hi
  rw [cuspScalarPencil_apply]
  exact sub_eq_iff_eq_add.mpr hi

/-- The scalar weak solution is unique whenever its actual pencil is a unit. -/
theorem cuspScalarPencilSolution_unique {z : ℂ} (hz : IsUnit (cuspScalarPencil z))
    (f : ModularHilbert) (u : cuspScalarForm)
    (hu : ∀ v : cuspScalarForm,
      inner ℂ (cuspScalarGradient v) (cuspScalarGradient u) -
        z * inner ℂ (scalarCuspEmbedding v) (scalarCuspEmbedding u) =
          inner ℂ (scalarCuspEmbedding v) f) :
    u = cuspScalarPencilSolution z f := by
  apply scalarCuspEmbedding_injective
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hz).1
  rw [cuspScalarPencil_apply_embedding_of_weak z f u hu,
    cuspScalarPencil_apply_embedding_of_weak z f (cuspScalarPencilSolution z f)
      (cuspScalarPencilSolution_equation hz f)]

end GapFamily.Analytic
