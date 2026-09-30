import GapFamily.Analytic.Modular.Elliptic.ModularLocalEvaluation
import GapFamily.Analytic.Foundation.AnalyticClosedSubspace
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Analytic packaging in the actual Laplacian graph

Orthogonal projection gives a bounded map to the complete Laplacian graph.
On genuine graph pairs it preserves both coordinates. Its action on operator
pairs is bounded in operator norm, so analytic candidate pairs give analytic
graph-valued operators and local continuous outputs.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient

open Set Dirichlet

/-- Orthogonal projection from the Hilbert product to the actual closed graph. -/
def laplacianGraphProjection :
    WithLp 2 (ModularHilbert × ModularHilbert) →L[ℂ] LaplacianGraphDomain :=
  (gradientGraph laplacian).orthogonalProjectionOnto

theorem laplacianGraphProjection_norm_le : ‖laplacianGraphProjection‖ ≤ 1 :=
  (gradientGraph laplacian).orthogonalProjectionOnto_norm_le

@[simp] theorem laplacianGraphProjection_subtype (u : LaplacianGraphDomain) :
    laplacianGraphProjection u = u :=
  (gradientGraph laplacian).orthogonalProjectionOnto_mem_subspace_eq_self u

/-- The same graph projection, with the ordinary product topology at its input. -/
def laplacianGraphPairMap :
    (ModularHilbert × ModularHilbert) →L[ℂ] LaplacianGraphDomain :=
  laplacianGraphProjection.comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert ModularHilbert).symm.toContinuousLinearMap

theorem laplacianGraphPairMap_eq_of_mem {u v : ModularHilbert}
    (h : (u, v) ∈ laplacian.graph) :
    laplacianGraphPairMap (u, v) = ⟨WithLp.toLp 2 (u, v), h⟩ :=
  laplacianGraphProjection_subtype ⟨WithLp.toLp 2 (u, v), h⟩

theorem laplacianGraphPairMap_embedding_of_mem {u v : ModularHilbert}
    (h : (u, v) ∈ laplacian.graph) :
    gradientEmbedding laplacian (laplacianGraphPairMap (u, v)) = u := by
  rw [laplacianGraphPairMap_eq_of_mem h]
  rfl

theorem laplacianGraphPairMap_value_of_mem {u v : ModularHilbert}
    (h : (u, v) ∈ laplacian.graph) :
    gradientValue laplacian (laplacianGraphPairMap (u, v)) = v := by
  rw [laplacianGraphPairMap_eq_of_mem h]
  rfl

theorem laplacianGraphPairMap_analyticAt {f g : ℂ → ModularHilbert} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    AnalyticAt ℂ (fun w => laplacianGraphPairMap (f w, g w)) z :=
  (laplacianGraphPairMap.analyticAt _).comp (hf.prod hg)

theorem laplacianGraphPairMap_analyticOnNhd {f g : ℂ → ModularHilbert} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) :
    AnalyticOnNhd ℂ (fun z => laplacianGraphPairMap (f z, g z)) U :=
  fun z hz => laplacianGraphPairMap_analyticAt (hf z hz) (hg z hz)

section Operator

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Bounded packaging of a value/operator-value pair, uniformly in its source. -/
def laplacianGraphOperator :
    ((E →L[ℂ] ModularHilbert) × (E →L[ℂ] ModularHilbert)) →L[ℂ]
      (E →L[ℂ] LaplacianGraphDomain) :=
  ((ContinuousLinearMap.compL ℂ E (ModularHilbert × ModularHilbert)
    LaplacianGraphDomain) laplacianGraphPairMap).comp
      (ContinuousLinearMap.prodₗᵢ ℂ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem laplacianGraphOperator_apply
    (S T : E →L[ℂ] ModularHilbert) (x : E) :
    laplacianGraphOperator E (S, T) x = laplacianGraphPairMap (S x, T x) := rfl

theorem laplacianGraphOperator_embedding
    (S T : E →L[ℂ] ModularHilbert) (h : ∀ x, (S x, T x) ∈ laplacian.graph) :
    (gradientEmbedding laplacian).comp (laplacianGraphOperator E (S, T)) = S := by
  apply ContinuousLinearMap.ext
  intro x
  exact laplacianGraphPairMap_embedding_of_mem (h x)

theorem laplacianGraphOperator_value
    (S T : E →L[ℂ] ModularHilbert) (h : ∀ x, (S x, T x) ∈ laplacian.graph) :
    (gradientValue laplacian).comp (laplacianGraphOperator E (S, T)) = T := by
  apply ContinuousLinearMap.ext
  intro x
  exact laplacianGraphPairMap_value_of_mem (h x)

theorem laplacianGraphOperator_analyticAt
    {S T : ℂ → E →L[ℂ] ModularHilbert} {z : ℂ}
    (hS : AnalyticAt ℂ S z) (hT : AnalyticAt ℂ T z) :
    AnalyticAt ℂ (fun w => laplacianGraphOperator E (S w, T w)) z := by
  have hp := ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := (E →L[ℂ] ModularHilbert) × (E →L[ℂ] ModularHilbert))
    (F := E →L[ℂ] LaplacianGraphDomain) (laplacianGraphOperator E) (S z, T z)
  exact hp.comp_of_eq (hS.prod hT) rfl

theorem laplacianGraphOperator_analyticOnNhd
    {S T : ℂ → E →L[ℂ] ModularHilbert} {U : Set ℂ}
    (hS : AnalyticOnNhd ℂ S U) (hT : AnalyticOnNhd ℂ T U) :
    AnalyticOnNhd ℂ (fun z => laplacianGraphOperator E (S z, T z)) U :=
  fun z hz => laplacianGraphOperator_analyticAt E (hS z hz) (hT z hz)

/-- The actual local continuous restriction after graph packaging. -/
def laplacianLocalOperator (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K)) :
    ((E →L[ℂ] ModularHilbert) × (E →L[ℂ] ModularHilbert)) →L[ℂ]
      (E →L[ℂ] C(K, ℂ)) :=
  ((ContinuousLinearMap.compL ℂ E LaplacianGraphDomain C(K, ℂ))
    (laplacianLocalRestriction K hKU hreg)).comp (laplacianGraphOperator E)

@[simp] theorem laplacianLocalOperator_apply (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    (S T : E →L[ℂ] ModularHilbert) (x : E) :
    laplacianLocalOperator E K hKU hreg (S, T) x =
      laplacianLocalRestriction K hKU hreg (laplacianGraphPairMap (S x, T x)) := rfl

theorem laplacianLocalOperator_analyticAt (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    {S T : ℂ → E →L[ℂ] ModularHilbert} {z : ℂ}
    (hS : AnalyticAt ℂ S z) (hT : AnalyticAt ℂ T z) :
    AnalyticAt ℂ (fun w => laplacianLocalOperator E K hKU hreg (S w, T w)) z := by
  have hp := ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := (E →L[ℂ] ModularHilbert) × (E →L[ℂ] ModularHilbert))
    (F := E →L[ℂ] C(K, ℂ)) (laplacianLocalOperator E K hKU hreg) (S z, T z)
  exact hp.comp_of_eq (hS.prod hT) rfl

theorem laplacianLocalOperator_analyticOnNhd (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    {S T : ℂ → E →L[ℂ] ModularHilbert} {U : Set ℂ}
    (hS : AnalyticOnNhd ℂ S U) (hT : AnalyticOnNhd ℂ T U) :
    AnalyticOnNhd ℂ (fun z => laplacianLocalOperator E K hKU hreg (S z, T z)) U :=
  fun z hz => laplacianLocalOperator_analyticAt E K hKU hreg (hS z hz) (hT z hz)

theorem laplacianLocalOperator_point_analyticAt (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K)) (x : K)
    {S T : ℂ → E →L[ℂ] ModularHilbert} {z : ℂ}
    (hS : AnalyticAt ℂ S z) (hT : AnalyticAt ℂ T z) :
    AnalyticAt ℂ (fun w => (ContinuousMap.evalCLM ℂ x).comp
      (laplacianLocalOperator E K hKU hreg (S w, T w))) z := by
  let Q : (E →L[ℂ] C(K, ℂ)) →L[ℂ] (E →L[ℂ] ℂ) :=
    ContinuousLinearMap.compL ℂ E C(K, ℂ) ℂ (ContinuousMap.evalCLM ℂ x)
  have hQ := ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := E →L[ℂ] C(K, ℂ)) (F := E →L[ℂ] ℂ) Q
    (laplacianLocalOperator E K hKU hreg (S z, T z))
  exact hQ.comp_of_eq (laplacianLocalOperator_analyticAt E K hKU hreg hS hT) rfl

theorem laplacianLocalOperator_point_analyticOnNhd (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K)) (x : K)
    {S T : ℂ → E →L[ℂ] ModularHilbert} {U : Set ℂ}
    (hS : AnalyticOnNhd ℂ S U) (hT : AnalyticOnNhd ℂ T U) :
    AnalyticOnNhd ℂ (fun z => (ContinuousMap.evalCLM ℂ x).comp
      (laplacianLocalOperator E K hKU hreg (S z, T z))) U :=
  fun z hz => laplacianLocalOperator_point_analyticAt E K hKU hreg x (hS z hz) (hT z hz)

theorem laplacianLocalOperator_ae_of_mem (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    (S T : E →L[ℂ] ModularHilbert) (h : ∀ x, (S x, T x) ∈ laplacian.graph) (x : E) :
    localContinuousExtend (laplacianLocalOperator E K hKU hreg (S, T) x)
      =ᵐ[MeasureTheory.volume.restrict K]
        (fun z => modularCoordinateEquiv.symm (S x) z) := by
  have ha := laplacianLocalRestriction_ae K hKU hreg
    (laplacianGraphPairMap (S x, T x))
  change localContinuousExtend (laplacianLocalOperator E K hKU hreg (S, T) x)
    =ᵐ[MeasureTheory.volume.restrict K]
      (fun z => modularCoordinateEquiv.symm
        (gradientEmbedding laplacian (laplacianGraphPairMap (S x, T x))) z) at ha
  rwa [laplacianGraphPairMap_embedding_of_mem (h x)] at ha

end Operator

end GapFamily.Analytic.ModularGradient
