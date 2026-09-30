import GapFamily.Analytic.Elliptic.LocalContinuousClosedGraph

/-!
# A closed-graph bound from ordinary Euclidean L² representatives

A linear map to continuous functions on a compact regular set is bounded
when it agrees almost everywhere with one fixed bounded map into global
ordinary Euclidean L². Strong L² convergence gives an almost-everywhere
convergent subsequence; density of the compact set's interior identifies the
continuous limit pointwise.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory
open scoped Topology

/-- Ordinary Euclidean L² representatives give a closed graph for the local
continuous representative map on every compact set with dense interior. -/
theorem localLpContinuousLinearMap_continuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {K : Set ℂ} (hK : IsCompact K) (hreg : K ⊆ closure (interior K))
    (J : V →L[ℂ] Lp ℂ 2 (volume : Measure ℂ)) (T : V →ₗ[ℂ] C(K, ℂ))
    (hT : ∀ u : V, localContinuousExtend (T u) =ᵐ[volume.restrict K]
      (fun z => J u z)) : Continuous T := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply T.continuous_of_seq_closed_graph
  intro v u g hv hTv
  have hJ : Tendsto (fun n => J (v n)) atTop (𝓝 (J u)) :=
    (J.continuous.tendsto u).comp hv
  have hm := tendstoInMeasure_of_tendsto_Lp hJ
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have hlocal : ∀ᵐ z ∂volume.restrict K,
      Tendsto (fun n => J (v (ns n)) z) atTop (𝓝 (J u z)) :=
    ae_restrict_of_ae hae
  have hall : ∀ᵐ z ∂volume.restrict K, ∀ n : ℕ,
      localContinuousExtend (T (v (ns n))) z = J (v (ns n)) z :=
    ae_all_iff.mpr (fun n => hT (v (ns n)))
  have hg : localContinuousExtend g =ᵐ[volume.restrict K] (fun z => J u z) := by
    filter_upwards [ae_restrict_mem hK.measurableSet, hlocal, hall] with z hz hlim heq
    have hp : Tendsto (fun n => T (v (ns n)) ⟨z, hz⟩) atTop (𝓝 (g ⟨z, hz⟩)) :=
      ((continuous_eval_const (⟨z, hz⟩ : K) :
        Continuous (fun f : C(K, ℂ) => f ⟨z, hz⟩)).tendsto g).comp
        (hTv.comp hns.tendsto_atTop)
    have hext : Tendsto (fun n => localContinuousExtend (T (v (ns n))) z)
        atTop (𝓝 (localContinuousExtend g z)) := by
      simpa only [localContinuousExtend_apply _ hz] using hp
    have hJlim : Tendsto (fun n => J (v (ns n)) z)
        atTop (𝓝 (localContinuousExtend g z)) := by
      simpa only [heq] using hext
    exact tendsto_nhds_unique hJlim hlim
  exact localContinuousMap_eq_of_ae hreg (hg.trans (hT u).symm)

/-- The local representative map bundled with its proved continuity. -/
def localLpContinuousLinearMap
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {K : Set ℂ} [CompactSpace K] (hreg : K ⊆ closure (interior K))
    (J : V →L[ℂ] Lp ℂ 2 (volume : Measure ℂ)) (T : V →ₗ[ℂ] C(K, ℂ))
    (hT : ∀ u : V, localContinuousExtend (T u) =ᵐ[volume.restrict K]
      (fun z => J u z)) : V →L[ℂ] C(K, ℂ) where
  toLinearMap := T
  cont := localLpContinuousLinearMap_continuous
    (isCompact_iff_compactSpace.mpr inferInstance) hreg J T hT

@[simp] theorem localLpContinuousLinearMap_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {K : Set ℂ} [CompactSpace K] (hreg : K ⊆ closure (interior K))
    (J : V →L[ℂ] Lp ℂ 2 (volume : Measure ℂ)) (T : V →ₗ[ℂ] C(K, ℂ))
    (hT : ∀ u : V, localContinuousExtend (T u) =ᵐ[volume.restrict K]
      (fun z => J u z)) (u : V) :
    localLpContinuousLinearMap hreg J T hT u = T u := rfl

/-- One finite constant controls every point of the compact observation set. -/
theorem exists_localLpContinuousLinearMap_point_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {K : Set ℂ} [CompactSpace K] (hreg : K ⊆ closure (interior K))
    (J : V →L[ℂ] Lp ℂ 2 (volume : Measure ℂ)) (T : V →ₗ[ℂ] C(K, ℂ))
    (hT : ∀ u : V, localContinuousExtend (T u) =ᵐ[volume.restrict K]
      (fun z => J u z)) :
    ∃ B : ℝ, 0 < B ∧ ∀ (u : V) (z : K), ‖T u z‖ ≤ B * ‖u‖ := by
  let A := localLpContinuousLinearMap hreg J T hT
  refine ⟨‖A‖ + 1, by positivity, fun u z => ?_⟩
  change ‖A u z‖ ≤ (‖A‖ + 1) * ‖u‖
  calc
    ‖A u z‖ ≤ ‖A u‖ := ContinuousMap.norm_coe_le_norm (A u) z
    _ ≤ ‖A‖ * ‖u‖ := A.le_opNorm u
    _ ≤ (‖A‖ + 1) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) (norm_nonneg u)

end GapFamily.Analytic
