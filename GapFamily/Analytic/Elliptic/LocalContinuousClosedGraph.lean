import GapFamily.Analytic.Modular.Geometry.ModularCoordinate
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.ContinuousMap.Compact

/-!
# A closed-graph bound for actual local continuous representatives

The continuous maps agree almost everywhere with one fixed bounded map into
the actual modular-coordinate L² space. Strong L² convergence supplies an
almost-everywhere convergent subsequence, identifying every function-space
limit. Regularity of the compact set then gives pointwise uniqueness.
-/

noncomputable section
namespace GapFamily.Analytic

open Set Filter MeasureTheory
open scoped Topology

/-- A continuous map on a set, extended by zero outside it. -/
def localContinuousExtend {K : Set ℂ} (f : C(K, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ K then f ⟨z, hz⟩ else 0

@[simp] theorem localContinuousExtend_apply {K : Set ℂ} (f : C(K, ℂ))
    {z : ℂ} (hz : z ∈ K) : localContinuousExtend f z = f ⟨z, hz⟩ := by
  simp [localContinuousExtend, hz]

theorem continuousOn_localContinuousExtend {K : Set ℂ} (f : C(K, ℂ)) :
    ContinuousOn (localContinuousExtend f) K := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : K.domRestrict (localContinuousExtend f) = f := by
    funext z
    exact localContinuousExtend_apply f z.property
  rw [he]
  exact f.continuous

/-- AE agreement determines a continuous map on a compact set with dense interior. -/
theorem localContinuousMap_eq_of_ae {K : Set ℂ}
    (hreg : K ⊆ closure (interior K)) {f g : C(K, ℂ)}
    (hfg : localContinuousExtend f =ᵐ[volume.restrict K] localContinuousExtend g) :
    f = g := by
  have he := Measure.eqOn_of_ae_eq hfg
    (continuousOn_localContinuousExtend f) (continuousOn_localContinuousExtend g) hreg
  apply ContinuousMap.ext
  intro z
  simpa only [localContinuousExtend_apply _ z.property] using he z.property

/-- A linear local representative map is continuous when its AE values agree
with an actual bounded modular-coordinate L² map. -/
theorem localContinuousLinearMap_continuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ modularInterior)
    (hreg : K ⊆ closure (interior K))
    (J : V →L[ℂ] ModularCoordinateHilbert) (T : V →ₗ[ℂ] C(K, ℂ))
    (hT : ∀ u : V, localContinuousExtend (T u) =ᵐ[volume.restrict K]
      (fun z => J u z)) : Continuous T := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply T.continuous_of_seq_closed_graph
  intro v u g hv hTv
  have hJ : Tendsto (fun n => J (v n)) atTop (𝓝 (J u)) :=
    (J.continuous.tendsto u).comp hv
  have hm := tendstoInMeasure_of_tendsto_Lp hJ
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have hvol : ∀ᵐ z ∂volume.restrict modularInterior,
      Tendsto (fun n => J (v (ns n)) z) atTop (𝓝 (J u z)) :=
    (ae_modularCoordinate_iff_restrict _).mp hae
  have hlocal : ∀ᵐ z ∂volume.restrict K,
      Tendsto (fun n => J (v (ns n)) z) atTop (𝓝 (J u z)) :=
    ae_restrict_of_ae_restrict_of_subset hKU hvol
  have hall : ∀ᵐ z ∂volume.restrict K, ∀ n : ℕ,
      localContinuousExtend (T (v (ns n))) z = J (v (ns n)) z :=
    ae_all_iff.mpr (fun n => hT (v (ns n)))
  have hg : localContinuousExtend g =ᵐ[volume.restrict K] (fun z => J u z) := by
    filter_upwards [ae_restrict_mem hK.measurableSet, hlocal, hall] with z hz hlim heq
    have hp : Tendsto (fun n => T (v (ns n)) ⟨z, hz⟩) atTop (𝓝 (g ⟨z, hz⟩)) :=
      ((continuous_eval_const (⟨z, hz⟩ : K) : Continuous (fun f : C(K, ℂ) => f ⟨z, hz⟩)).tendsto g).comp
        (hTv.comp hns.tendsto_atTop)
    have hext : Tendsto (fun n => localContinuousExtend (T (v (ns n))) z)
        atTop (𝓝 (localContinuousExtend g z)) := by
      simpa only [localContinuousExtend_apply _ hz] using hp
    have hJlim : Tendsto (fun n => J (v (ns n)) z)
        atTop (𝓝 (localContinuousExtend g z)) := by
      simpa only [heq] using hext
    exact tendsto_nhds_unique hJlim hlim
  exact localContinuousMap_eq_of_ae hreg (hg.trans (hT u).symm)

/-- The same proved local map bundled as a continuous linear operator. -/
def localContinuousLinearMap
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {K : Set ℂ} [CompactSpace K] (hKU : K ⊆ modularInterior)
    (hreg : K ⊆ closure (interior K))
    (J : V →L[ℂ] ModularCoordinateHilbert) (T : V →ₗ[ℂ] C(K, ℂ))
    (hT : ∀ u : V, localContinuousExtend (T u) =ᵐ[volume.restrict K]
      (fun z => J u z)) : V →L[ℂ] C(K, ℂ) where
  toLinearMap := T
  cont := localContinuousLinearMap_continuous
    (isCompact_iff_compactSpace.mpr inferInstance) hKU hreg J T hT

@[simp] theorem localContinuousLinearMap_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {K : Set ℂ} [CompactSpace K] (hKU : K ⊆ modularInterior)
    (hreg : K ⊆ closure (interior K))
    (J : V →L[ℂ] ModularCoordinateHilbert) (T : V →ₗ[ℂ] C(K, ℂ))
    (hT : ∀ u : V, localContinuousExtend (T u) =ᵐ[volume.restrict K]
      (fun z => J u z)) (u : V) :
    localContinuousLinearMap hKU hreg J T hT u = T u := rfl

end GapFamily.Analytic
