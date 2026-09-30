import Mathlib.Analysis.InnerProductSpace.ProdL2
import GapFamily.Analytic.Elliptic.DirichletForm

/-!
# Hilbert graph space of a closed gradient

The graph of a partially defined gradient carries the exact energy-plus-mass
inner product. Its first coordinate embeds it contractively into the ambient
space. Closedness of the gradient proves completeness, while density of the
gradient domain proves density of the embedding.
-/

namespace GapFamily.Analytic.Dirichlet

open scoped InnerProductSpace

noncomputable section

variable {H G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The actual gradient graph with its Hilbert product norm. -/
def gradientGraph (D : H →ₗ.[ℂ] G) : Submodule ℂ (WithLp 2 (H × G)) :=
  D.graph.comap (WithLp.linearEquiv 2 ℂ (H × G)).toLinearMap

theorem gradientGraph_isClosed (D : H →ₗ.[ℂ] G) (hD : D.IsClosed) :
    IsClosed (gradientGraph D : Set (WithLp 2 (H × G))) :=
  hD.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H G).continuous

/-- A closed gradient has a complete energy-plus-mass graph space. -/
theorem gradientGraph_completeSpace [CompleteSpace H] [CompleteSpace G]
    (D : H →ₗ.[ℂ] G) (hD : D.IsClosed) : CompleteSpace (gradientGraph D) :=
  (gradientGraph_isClosed D hD).isComplete.completeSpace_coe

/-- The first graph coordinate is the ambient vector. -/
def gradientEmbedding (D : H →ₗ.[ℂ] G) : gradientGraph D →L[ℂ] H :=
  (WithLp.fstL 2 ℂ H G).comp (gradientGraph D).subtypeL

/-- The second graph coordinate is the gradient value. -/
def gradientValue (D : H →ₗ.[ℂ] G) : gradientGraph D →L[ℂ] G :=
  (WithLp.sndL 2 ℂ H G).comp (gradientGraph D).subtypeL

/-- Every vector in the gradient domain has its canonical graph lift. -/
def gradientLift (D : H →ₗ.[ℂ] G) (x : D.domain) : gradientGraph D :=
  ⟨WithLp.toLp 2 ((x : H), D x), D.mem_graph x⟩

@[simp] theorem gradientEmbedding_lift (D : H →ₗ.[ℂ] G) (x : D.domain) :
    gradientEmbedding D (gradientLift D x) = x := rfl

@[simp] theorem gradientValue_lift (D : H →ₗ.[ℂ] G) (x : D.domain) :
    gradientValue D (gradientLift D x) = D x := rfl

theorem gradientEmbedding_mem_domain (D : H →ₗ.[ℂ] G) (u : gradientGraph D) :
    gradientEmbedding D u ∈ D.domain := by
  obtain ⟨v, hv, _⟩ := D.mem_graph_iff.mp u.property
  change (v : H) = (WithLp.ofLp u.val).1 at hv
  change (WithLp.ofLp u.val).1 ∈ D.domain
  rw [← hv]
  exact v.property

/-- The second coordinate is the actual partially defined gradient, not a separate map. -/
theorem gradientValue_apply (D : H →ₗ.[ℂ] G) (u : gradientGraph D) :
    gradientValue D u = D ⟨gradientEmbedding D u, gradientEmbedding_mem_domain D u⟩ := by
  exact D.mem_graph_snd_inj' u.property (D.mem_graph _) rfl

theorem gradientEmbedding_injective (D : H →ₗ.[ℂ] G) :
    Function.Injective (gradientEmbedding D) := by
  intro u v huv
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℂ (H × G)).injective
  apply Prod.ext
  · exact huv
  · exact D.mem_graph_snd_inj' u.property v.property huv

@[simp] theorem gradientLift_embedding (D : H →ₗ.[ℂ] G) (u : gradientGraph D) :
    gradientLift D ⟨gradientEmbedding D u, gradientEmbedding_mem_domain D u⟩ = u :=
  gradientEmbedding_injective D rfl

theorem gradientEmbedding_range (D : H →ₗ.[ℂ] G) :
    Set.range (gradientEmbedding D) = (D.domain : Set H) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact gradientEmbedding_mem_domain D u
  · intro hx
    exact ⟨gradientLift D ⟨x, hx⟩, rfl⟩

theorem gradientEmbedding_denseRange (D : H →ₗ.[ℂ] G)
    (hD : Dense (D.domain : Set H)) : DenseRange (gradientEmbedding D) := by
  change Dense (Set.range (gradientEmbedding D))
  rw [gradientEmbedding_range]
  exact hD

theorem gradientEmbedding_norm_le (D : H →ₗ.[ℂ] G) (u : gradientGraph D) :
    ‖gradientEmbedding D u‖ ≤ ‖u‖ :=
  WithLp.norm_fst_le H u.val

theorem gradientValue_norm_le (D : H →ₗ.[ℂ] G) (u : gradientGraph D) :
    ‖gradientValue D u‖ ≤ ‖u‖ :=
  WithLp.norm_snd_le H u.val

theorem gradientEmbedding_norm_le_one (D : H →ₗ.[ℂ] G) :
    ‖gradientEmbedding D‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using gradientEmbedding_norm_le D u

theorem gradientValue_norm_le_one (D : H →ₗ.[ℂ] G) :
    ‖gradientValue D‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using gradientValue_norm_le D u

theorem gradientGraph_inner (D : H →ₗ.[ℂ] G) (u v : gradientGraph D) :
    ⟪u, v⟫_ℂ = ⟪gradientEmbedding D u, gradientEmbedding D v⟫_ℂ +
      ⟪gradientValue D u, gradientValue D v⟫_ℂ := rfl

theorem gradientGraph_norm_sq (D : H →ₗ.[ℂ] G) (u : gradientGraph D) :
    ‖u‖ ^ 2 = ‖gradientEmbedding D u‖ ^ 2 + ‖gradientValue D u‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.val

/-- The abstract complete-domain energy is exactly the gradient inner product. -/
theorem gradient_formEnergy (D : H →ₗ.[ℂ] G) (u v : gradientGraph D) :
    formEnergy (gradientEmbedding D) u v = ⟪gradientValue D u, gradientValue D v⟫_ℂ := by
  rw [formEnergy, gradientGraph_inner]
  ring

end

end GapFamily.Analytic.Dirichlet
