import GapFamily.Analytic.Modular.Elliptic.ModularUpperEllipticContinuous
import GapFamily.Analytic.Modular.Elliptic.ModularLocalEvaluation
import GapFamily.Analytic.Elliptic.LocalLpContinuousClosedGraph

/-!
# Graph-norm evaluation on upper-half-plane cutoff plateaus

The weak equation across all modular seams supplies local continuous
representatives. The actual Hilbert cutoff map controls their Euclidean L²
values, so a closed-graph argument makes restriction to a regular compact
upper chart a bounded map from the actual Laplacian graph domain.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set Filter MeasureTheory Dirichlet UpperHalfPlane
open scoped Topology ContDiff

variable (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
  (hsχ : tsupport χ ⊆ upperHalfPlaneSet)

/-- The actual graph value in ordinary Euclidean L² after a compact upper cutoff. -/
def laplacianUpperGraphValue :
    LaplacianGraphDomain →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  (upperCutoffHilbertValueOperator χ hχ hcχ hsχ).comp (gradientEmbedding laplacian)

theorem laplacianUpperGraphValue_eq_elliptic (u : LaplacianGraphDomain) :
    (fun z => laplacianUpperGraphValue χ hχ hcχ hsχ u z) =
      upperEllipticValue χ hχ hcχ hsχ
        ⟨gradientEmbedding laplacian u, gradientEmbedding_mem_domain laplacian u⟩ := by
  have h := upperCutoffHilbertValueOperator_formEmbedding χ hχ hcχ hsχ
    (formLift ⟨gradientEmbedding laplacian u,
      laplacian_domain_le (gradientEmbedding_mem_domain laplacian u)⟩)
  simpa only [formEmbedding, formLift, gradientEmbedding_lift,
    laplacianUpperGraphValue, ContinuousLinearMap.comp_apply, upperEllipticValue] using
    congrArg (fun f : Lp ℂ 2 (volume : Measure ℂ) => (fun z => f z)) h

variable (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
include hU hχU

theorem laplacianUpperGraph_exists_continuousRepresentative (u : LaplacianGraphDomain) :
    ∃ G : ℂ → ℂ, ContinuousOn G U ∧
      G =ᵐ[volume.restrict U] (fun z => laplacianUpperGraphValue χ hχ hcχ hsχ u z) := by
  rw [laplacianUpperGraphValue_eq_elliptic]
  exact laplacian_upper_exists_continuousRepresentative χ hχ hcχ hsχ U hU hχU
    ⟨gradientEmbedding laplacian u, gradientEmbedding_mem_domain laplacian u⟩

def laplacianUpperRepresentative (u : LaplacianGraphDomain) : ℂ → ℂ :=
  (laplacianUpperGraph_exists_continuousRepresentative χ hχ hcχ hsχ U hU hχU u).choose

theorem laplacianUpperRepresentative_continuousOn (u : LaplacianGraphDomain) :
    ContinuousOn (laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u) U :=
  (laplacianUpperGraph_exists_continuousRepresentative χ hχ hcχ hsχ U hU hχU u).choose_spec.1

theorem laplacianUpperRepresentative_ae (u : LaplacianGraphDomain) :
    laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u =ᵐ[volume.restrict U]
      (fun z => laplacianUpperGraphValue χ hχ hcχ hsχ u z) :=
  (laplacianUpperGraph_exists_continuousRepresentative χ hχ hcχ hsχ U hU hχU u).choose_spec.2

theorem laplacianUpperRepresentative_add (u v : LaplacianGraphDomain) :
    EqOn (laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU (u + v))
      (laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u +
        laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU v) U := by
  apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hU
    (laplacianUpperRepresentative_continuousOn χ hχ hcχ hsχ U hU hχU (u + v))
    ((laplacianUpperRepresentative_continuousOn χ hχ hcχ hsχ U hU hχU u).add
      (laplacianUpperRepresentative_continuousOn χ hχ hcχ hsχ U hU hχU v))
  have ha := ae_restrict_of_ae (μ := (volume : Measure ℂ)) (s := U)
    (Lp.coeFn_add (laplacianUpperGraphValue χ hχ hcχ hsχ u)
      (laplacianUpperGraphValue χ hχ hcχ hsχ v))
  filter_upwards [laplacianUpperRepresentative_ae χ hχ hcχ hsχ U hU hχU (u + v),
    laplacianUpperRepresentative_ae χ hχ hcχ hsχ U hU hχU u,
    laplacianUpperRepresentative_ae χ hχ hcχ hsχ U hU hχU v, ha]
      with z huv hu hv ha
  change laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU (u + v) z =
    laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u z +
      laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU v z
  rw [huv, hu, hv, map_add, ha]
  rfl

theorem laplacianUpperRepresentative_smul (c : ℂ) (u : LaplacianGraphDomain) :
    EqOn (laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU (c • u))
      (c • laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u) U := by
  apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hU
    (laplacianUpperRepresentative_continuousOn χ hχ hcχ hsχ U hU hχU (c • u))
    ((laplacianUpperRepresentative_continuousOn χ hχ hcχ hsχ U hU hχU u).const_smul c)
  have hs := ae_restrict_of_ae (μ := (volume : Measure ℂ)) (s := U)
    (Lp.coeFn_smul c (laplacianUpperGraphValue χ hχ hcχ hsχ u))
  filter_upwards [laplacianUpperRepresentative_ae χ hχ hcχ hsχ U hU hχU (c • u),
    laplacianUpperRepresentative_ae χ hχ hcχ hsχ U hU hχU u, hs] with z hcu hu hs
  change laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU (c • u) z =
    c • laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u z
  rw [hcu, hu, map_smul, hs]
  rfl

/-- Restriction of the actual seam-continuous graph representative. -/
def laplacianUpperLocalMap (K : Set ℂ) (hKU : K ⊆ U) :
    LaplacianGraphDomain →ₗ[ℂ] C(K, ℂ) where
  toFun u := ⟨fun z => laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u z,
    (laplacianUpperRepresentative_continuousOn χ hχ hcχ hsχ U hU hχU u).comp_continuous
      continuous_subtype_val (fun z => hKU z.property)⟩
  map_add' u v := by
    apply ContinuousMap.ext
    intro z
    exact laplacianUpperRepresentative_add χ hχ hcχ hsχ U hU hχU u v (hKU z.property)
  map_smul' c u := by
    apply ContinuousMap.ext
    intro z
    exact laplacianUpperRepresentative_smul χ hχ hcχ hsχ U hU hχU c u (hKU z.property)

theorem laplacianUpperLocalMap_ae {K : Set ℂ} (hK : MeasurableSet K)
    (hKU : K ⊆ U) (u : LaplacianGraphDomain) :
    localContinuousExtend (laplacianUpperLocalMap χ hχ hcχ hsχ U hU hχU K hKU u)
      =ᵐ[volume.restrict K] (fun z => laplacianUpperGraphValue χ hχ hcχ hsχ u z) := by
  filter_upwards [ae_restrict_mem hK, ae_restrict_of_ae_restrict_of_subset hKU
    (laplacianUpperRepresentative_ae χ hχ hcχ hsχ U hU hχU u)] with z hz heq
  rw [localContinuousExtend_apply _ hz]
  exact heq

/-- Actual graph-norm continuous evaluation on every regular compact upper chart. -/
def laplacianUpperLocalRestriction (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) (hreg : K ⊆ closure (interior K)) :
    LaplacianGraphDomain →L[ℂ] C(K, ℂ) :=
  localLpContinuousLinearMap hreg (laplacianUpperGraphValue χ hχ hcχ hsχ)
    (laplacianUpperLocalMap χ hχ hcχ hsχ U hU hχU K hKU)
    (laplacianUpperLocalMap_ae χ hχ hcχ hsχ U hU hχU
      (isCompact_iff_compactSpace.mpr inferInstance).measurableSet hKU)

theorem laplacianUpperLocalRestriction_ae (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) (hreg : K ⊆ closure (interior K)) (u : LaplacianGraphDomain) :
    localContinuousExtend (laplacianUpperLocalRestriction χ hχ hcχ hsχ U hU hχU K hKU hreg u)
      =ᵐ[volume.restrict K] (fun z => laplacianUpperGraphValue χ hχ hcχ hsχ u z) :=
  laplacianUpperLocalMap_ae χ hχ hcχ hsχ U hU hχU
    (isCompact_iff_compactSpace.mpr inferInstance).measurableSet hKU u

theorem laplacianUpperLocalRestriction_bound (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ U) (hreg : K ⊆ closure (interior K)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : LaplacianGraphDomain) (z : K),
      ‖laplacianUpperLocalRestriction χ hχ hcχ hsχ U hU hχU K hKU hreg u z‖ ≤ C * ‖u‖ :=
  exists_localLpContinuousLinearMap_point_bound hreg
    (laplacianUpperGraphValue χ hχ hcχ hsχ)
    (laplacianUpperLocalMap χ hχ hcχ hsχ U hU hχU K hKU)
    (laplacianUpperLocalMap_ae χ hχ hcχ hsχ U hU hχU
      (isCompact_iff_compactSpace.mpr inferInstance).measurableSet hKU)

/-- Evaluation agrees with any genuine continuous representative of the same
actual local field; no chosen pointwise version of an L² class is assumed. -/
theorem laplacianUpperLocalRestriction_eq_localRepresentative
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (hreg : K ⊆ closure (interior K))
    (z : K) (u : LaplacianGraphDomain) {V : Set ℂ} (hV : IsOpen V)
    (hz : (z : ℂ) ∈ V) (hVU : V ⊆ U) {G : ℂ → ℂ} (hG : ContinuousOn G V)
    (hGae : G =ᵐ[volume.restrict V] (fun w => laplacianUpperGraphValue χ hχ hcχ hsχ u w)) :
    laplacianUpperLocalRestriction χ hχ hcχ hsχ U hU hχU K hKU hreg u z = G z := by
  have hr : laplacianUpperRepresentative χ hχ hcχ hsχ U hU hχU u
      =ᵐ[volume.restrict V] (fun w => laplacianUpperGraphValue χ hχ hcχ hsχ u w) :=
    ae_restrict_of_ae_restrict_of_subset hVU
      (laplacianUpperRepresentative_ae χ hχ hcχ hsχ U hU hχU u)
  exact Measure.eqOn_open_of_ae_eq (μ := volume) (hr.trans hGae.symm) hV
    ((laplacianUpperRepresentative_continuousOn χ hχ hcχ hsχ U hU hχU u).mono hVU) hG hz

end GapFamily.Analytic.ModularGradient
