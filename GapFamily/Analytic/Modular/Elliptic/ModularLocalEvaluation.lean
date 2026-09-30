import GapFamily.Analytic.Modular.Elliptic.ModularEllipticContinuous
import GapFamily.Analytic.Elliptic.LocalContinuousRepresentative
import GapFamily.Analytic.Elliptic.LocalContinuousClosedGraph
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Actual local evaluation in the modular operator graph norm

The continuous representative is constructed by gluing the proved local
representatives of actual Laplacian-domain vectors. The closed-graph theorem
then bounds its restriction to each regular compact interior set.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient

open Set Filter MeasureTheory Dirichlet
open scoped Topology

abbrev LaplacianGraphDomain := gradientGraph laplacian

instance : CompleteSpace LaplacianGraphDomain :=
  gradientGraph_completeSpace laplacian laplacian_isClosed

/-- The actual graph vector's modular value in ordinary complex coordinates. -/
def laplacianGraphCoordinate : LaplacianGraphDomain →L[ℂ] ModularCoordinateHilbert :=
  modularCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (gradientEmbedding laplacian)

theorem laplacianGraph_norm_sq (u : LaplacianGraphDomain) :
    ‖u‖^2 = ‖gradientEmbedding laplacian u‖^2 +
      ‖laplacian ⟨gradientEmbedding laplacian u, gradientEmbedding_mem_domain laplacian u⟩‖^2 := by
  rw [gradientGraph_norm_sq, gradientValue_apply]

/-- Local regularity of the actual operator gives a global continuous
representative on the modular interior, by proved AE-compatible gluing. -/
theorem laplacianGraph_exists_continuousRepresentative (u : LaplacianGraphDomain) :
    ∃ G : ℂ → ℂ, ContinuousOn G modularInterior ∧
      G =ᵐ[volume.restrict modularInterior] (fun z => laplacianGraphCoordinate u z) := by
  apply exists_continuousOn_ae_eq_of_locally modularInterior isOpen_modularInterior
  intro z hz
  obtain ⟨V, hVo, hzV, _hVc, hVU, G, hGc, hGae⟩ :=
    laplacian_exists_local_continuousRepresentative
      ⟨gradientEmbedding laplacian u, gradientEmbedding_mem_domain laplacian u⟩ z hz
  exact ⟨V, hVo, hzV, (fun w hw => hVU (subset_closure hw)), G, hGc, hGae⟩

def laplacianInteriorRepresentative (u : LaplacianGraphDomain) : ℂ → ℂ :=
  (laplacianGraph_exists_continuousRepresentative u).choose

theorem laplacianInteriorRepresentative_continuousOn (u : LaplacianGraphDomain) :
    ContinuousOn (laplacianInteriorRepresentative u) modularInterior :=
  (laplacianGraph_exists_continuousRepresentative u).choose_spec.1

theorem laplacianInteriorRepresentative_ae (u : LaplacianGraphDomain) :
    laplacianInteriorRepresentative u =ᵐ[volume.restrict modularInterior]
      (fun z => laplacianGraphCoordinate u z) :=
  (laplacianGraph_exists_continuousRepresentative u).choose_spec.2

theorem laplacianInteriorRepresentative_add (u v : LaplacianGraphDomain) :
    EqOn (laplacianInteriorRepresentative (u + v))
      (laplacianInteriorRepresentative u + laplacianInteriorRepresentative v) modularInterior := by
  apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_modularInterior
    (laplacianInteriorRepresentative_continuousOn (u + v))
    ((laplacianInteriorRepresentative_continuousOn u).add
      (laplacianInteriorRepresentative_continuousOn v))
  have ha := (ae_modularCoordinate_iff_restrict _).mp
    (Lp.coeFn_add (laplacianGraphCoordinate u) (laplacianGraphCoordinate v))
  filter_upwards [laplacianInteriorRepresentative_ae (u + v),
    laplacianInteriorRepresentative_ae u, laplacianInteriorRepresentative_ae v, ha]
    with z huv hu hv ha
  change laplacianInteriorRepresentative (u + v) z =
    laplacianInteriorRepresentative u z + laplacianInteriorRepresentative v z
  rw [huv, hu, hv, map_add, ha]
  rfl

theorem laplacianInteriorRepresentative_smul (c : ℂ) (u : LaplacianGraphDomain) :
    EqOn (laplacianInteriorRepresentative (c • u))
      (c • laplacianInteriorRepresentative u) modularInterior := by
  apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_modularInterior
    (laplacianInteriorRepresentative_continuousOn (c • u))
    ((laplacianInteriorRepresentative_continuousOn u).const_smul c)
  have hs := (ae_modularCoordinate_iff_restrict _).mp
    (Lp.coeFn_smul c (laplacianGraphCoordinate u))
  filter_upwards [laplacianInteriorRepresentative_ae (c • u),
    laplacianInteriorRepresentative_ae u, hs] with z hcu hu hs
  change laplacianInteriorRepresentative (c • u) z = c • laplacianInteriorRepresentative u z
  rw [hcu, hu, map_smul, hs]
  rfl

/-- The constructed continuous representative restricted to a fixed interior set. -/
def laplacianLocalMap (K : Set ℂ) (hKU : K ⊆ modularInterior) :
    LaplacianGraphDomain →ₗ[ℂ] C(K, ℂ) where
  toFun u := ⟨fun z => laplacianInteriorRepresentative u z,
    (laplacianInteriorRepresentative_continuousOn u).comp_continuous
      continuous_subtype_val (fun z => hKU z.property)⟩
  map_add' u v := by
    apply ContinuousMap.ext
    intro z
    exact laplacianInteriorRepresentative_add u v (hKU z.property)
  map_smul' c u := by
    apply ContinuousMap.ext
    intro z
    exact laplacianInteriorRepresentative_smul c u (hKU z.property)

theorem laplacianLocalMap_ae {K : Set ℂ} (hK : MeasurableSet K)
    (hKU : K ⊆ modularInterior) (u : LaplacianGraphDomain) :
    localContinuousExtend (laplacianLocalMap K hKU u) =ᵐ[volume.restrict K]
      (fun z => laplacianGraphCoordinate u z) := by
  filter_upwards [ae_restrict_mem hK,
    ae_restrict_of_ae_restrict_of_subset hKU (laplacianInteriorRepresentative_ae u)]
      with z hz heq
  rw [localContinuousExtend_apply _ hz]
  exact heq

/-- A genuine local continuous linear restriction on the actual complete
Laplacian graph domain. Regularity of `K` rules out invisible thin parts. -/
def laplacianLocalRestriction (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K)) :
    LaplacianGraphDomain →L[ℂ] C(K, ℂ) :=
  ⟨laplacianLocalMap K hKU,
    localContinuousLinearMap_continuous
      (isCompact_iff_compactSpace.mpr inferInstance) hKU hreg laplacianGraphCoordinate
      (laplacianLocalMap K hKU)
      (laplacianLocalMap_ae (isCompact_iff_compactSpace.mpr inferInstance).measurableSet hKU)⟩

theorem laplacianLocalRestriction_ae (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K)) (u : LaplacianGraphDomain) :
    localContinuousExtend (laplacianLocalRestriction K hKU hreg u) =ᵐ[volume.restrict K]
      (fun z => laplacianGraphCoordinate u z) :=
  laplacianLocalMap_ae (isCompact_iff_compactSpace.mpr inferInstance).measurableSet hKU u

/-- A fixed regular compact interior target has a finite uniform point bound
by the actual operator graph norm. -/
theorem laplacianLocalRestriction_bound (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : LaplacianGraphDomain) (z : K),
      ‖laplacianLocalRestriction K hKU hreg u z‖ ≤ C * ‖u‖ := by
  let T := laplacianLocalRestriction K hKU hreg
  refine ⟨‖T‖ + 1, by positivity, fun u z => ?_⟩
  exact ((T u).norm_coe_le_norm z).trans ((T.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (by linarith : ‖T‖ ≤ ‖T‖ + 1) (norm_nonneg u)))

end GapFamily.Analytic.ModularGradient
