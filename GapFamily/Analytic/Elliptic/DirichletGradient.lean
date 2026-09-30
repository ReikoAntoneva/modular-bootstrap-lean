import GapFamily.Analytic.Elliptic.GradientGraph

/-!
# The nonnegative operator of a closed gradient

A densely defined closed linear gradient determines its actual complete graph
form domain. The form construction then produces a self-adjoint nonnegative
operator, identified with the adjoint-gradient composition on its exact domain.
-/

namespace GapFamily.Analytic.Dirichlet

open scoped InnerProductSpace

noncomputable section

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (D : H →ₗ.[ℂ] G) (hD : D.IsClosed) (hd : Dense (D.domain : Set H))

/-- The nonnegative operator constructed from the closed gradient's graph norm. -/
abbrev closedGradientOperator : H →ₗ.[ℂ] H := by
  let := gradientGraph_completeSpace D hD
  exact formOperator (gradientEmbedding D) (gradientEmbedding_denseRange D hd)

theorem closedGradientOperator_isSelfAdjoint :
    IsSelfAdjoint (closedGradientOperator D hD hd) := by
  let := gradientGraph_completeSpace D hD
  exact formOperator_isSelfAdjoint (gradientEmbedding D) (gradientEmbedding_denseRange D hd)

theorem closedGradientOperator_isClosed : (closedGradientOperator D hD hd).IsClosed :=
  (closedGradientOperator_isSelfAdjoint D hD hd).isClosed

theorem closedGradientOperator_dense_domain :
    Dense ((closedGradientOperator D hD hd).domain : Set H) :=
  (closedGradientOperator_isSelfAdjoint D hD hd).dense_domain

theorem closedGradientOperator_nonnegative (u : (closedGradientOperator D hD hd).domain) :
    0 ≤ (inner ℂ (closedGradientOperator D hD hd u) (u : H)).re := by
  let := gradientGraph_completeSpace D hD
  exact formOperator_nonnegative (gradientEmbedding D) (gradientEmbedding_denseRange D hd)
    (gradientEmbedding_norm_le_one D) u

/-- Every operator-domain vector belongs to the original gradient domain. -/
theorem closedGradientOperator_domain_le : (closedGradientOperator D hD hd).domain ≤ D.domain := by
  let := gradientGraph_completeSpace D hD
  intro u hu
  let U : (closedGradientOperator D hD hd).domain := ⟨u, hu⟩
  let v := formOperatorLift (gradientEmbedding D) (gradientEmbedding_denseRange D hd) U
  have hv := gradientEmbedding_mem_domain D v
  simpa only [v, formOperatorLift_embedding] using hv

/-- The associated operator represents the actual gradient energy. -/
theorem closedGradientOperator_representation
    (u : (closedGradientOperator D hD hd).domain) (v : D.domain) :
    inner ℂ (closedGradientOperator D hD hd u) (v : H) =
      inner ℂ (D ⟨u, closedGradientOperator_domain_le D hD hd u.property⟩) (D v) := by
  let := gradientGraph_completeSpace D hD
  have h := formOperator_representation (gradientEmbedding D)
    (gradientEmbedding_denseRange D hd) u (gradientLift D v)
  rw [gradientEmbedding_lift, gradient_formEnergy, gradientValue_lift] at h
  simpa only [gradientValue_apply, formOperatorLift_embedding] using h

/-- The exact operator domain is the domain of the adjoint-gradient composition. -/
theorem closedGradientOperator_domain_iff (u : D.domain) :
    (u : H) ∈ (closedGradientOperator D hD hd).domain ↔ D u ∈ D.adjoint.domain := by
  let := gradientGraph_completeSpace D hD
  constructor
  · intro hu
    apply D.mem_adjoint_domain_of_exists
    refine ⟨closedGradientOperator D hD hd ⟨u, hu⟩, ?_⟩
    intro v
    exact closedGradientOperator_representation D hD hd ⟨u, hu⟩ v
  · intro hu
    have hf : ∀ v : gradientGraph D,
        formEnergy (gradientEmbedding D) (gradientLift D u) v =
          inner ℂ (D.adjoint ⟨D u, hu⟩) (gradientEmbedding D v) := by
      intro v
      rw [gradient_formEnergy, gradientValue_lift, gradientValue_apply]
      exact (D.adjoint_isFormalAdjoint hd ⟨D u, hu⟩
        ⟨gradientEmbedding D v, gradientEmbedding_mem_domain D v⟩).symm
    have h := (formOperator_domain_iff (gradientEmbedding D)
      (gradientEmbedding_denseRange D hd) (gradientEmbedding_injective D) (gradientLift D u)).mpr
        ⟨D.adjoint ⟨D u, hu⟩, hf⟩
    simpa only [gradientEmbedding_lift] using h

/-- The constructed self-adjoint operator has the literal value `D† (D u)`. -/
theorem closedGradientOperator_value (u : D.domain) (hu : D u ∈ D.adjoint.domain) :
    closedGradientOperator D hD hd
      ⟨u, (closedGradientOperator_domain_iff D hD hd u).mpr hu⟩ = D.adjoint ⟨D u, hu⟩ := by
  symm
  apply D.adjoint_apply_eq hd
  intro v
  exact closedGradientOperator_representation D hD hd _ v

/-- The nonnegative operator has precisely the zero-gradient vectors as its kernel. -/
theorem closedGradientOperator_kernel : (closedGradientOperator D hD hd).ker = D.ker := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, rfl, hu⟩ := LinearPMap.mem_ker_iff.mp hx
    let v : D.domain := ⟨u, closedGradientOperator_domain_le D hD hd u.property⟩
    refine LinearPMap.mem_ker_iff.mpr ⟨v, rfl, ?_⟩
    have h := closedGradientOperator_representation D hD hd u v
    rw [hu, inner_zero_left] at h
    exact inner_self_eq_zero.mp h.symm
  · intro hx
    obtain ⟨u, rfl, hu⟩ := LinearPMap.mem_ker_iff.mp hx
    have hmem : D u ∈ D.adjoint.domain := hu ▸ D.adjoint.domain.zero_mem
    let v : (closedGradientOperator D hD hd).domain :=
      ⟨u, (closedGradientOperator_domain_iff D hD hd u).mpr hmem⟩
    refine LinearPMap.mem_ker_iff.mpr ⟨v, rfl, ?_⟩
    have h := closedGradientOperator_value D hD hd u hmem
    have hz : (⟨D u, hmem⟩ : D.adjoint.domain) = 0 := Subtype.ext hu
    simpa only [hz, LinearPMap.map_zero] using h

end

end GapFamily.Analytic.Dirichlet
