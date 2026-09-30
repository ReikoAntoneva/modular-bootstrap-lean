import GapFamily.Analytic.Foundation.VaryingSupportAverage
import GapFamily.Analytic.Elliptic.LocalContinuousClosedGraph
import GapFamily.Analytic.Modular.Geometry.ModularSeamCoordinate

noncomputable section

namespace GapFamily.Analytic.SpatialPoint

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

/-- Source averaging converges in the compact target supremum norm, which
controls the target average uniformly even when both radii shrink together.
Every integral is locally integrable by compactness and continuity. -/
theorem tendsto_double_setAverage_ball
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    {K : Set ℂ} [CompactSpace K] {c : X → ℂ} (hc : Continuous c)
    (hL : IsCompact (c ⁻¹' K)) {V : X → C(K, ℂ)}
    (hV : ContinuousOn V (c ⁻¹' K))
    {p q : X} (hp : p ∈ μ.support) (hq : q ∈ μ.support)
    {R : ℝ} (hR : 0 < R)
    (hpR : Metric.ball p R ⊆ c ⁻¹' K)
    (hqR : Metric.ball q R ⊆ c ⁻¹' K) :
    Tendsto
      (fun r : ℝ => ⨍ z in Metric.ball p r,
        localContinuousExtend (⨍ w in Metric.ball q r, V w ∂μ) (c z) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (localContinuousExtend (V q) (c p))) := by
  have hpL : c ⁻¹' K ∈ 𝓝 p :=
    mem_of_superset (Metric.ball_mem_nhds p hR) hpR
  have hqL : c ⁻¹' K ∈ 𝓝 q :=
    mem_of_superset (Metric.ball_mem_nhds q hR) hqR
  have hiV : IntegrableOn V (Metric.ball q R) μ :=
    (hV.integrableOn_compact hL).mono_set hqR
  have hvavg := SupportAverage.tendsto_setAverage_ball μ hR hiV
    (hV.continuousAt hqL) hq
  have hcont (g : C(K, ℂ)) :
      ContinuousOn (fun z : X => localContinuousExtend g (c z)) (c ⁻¹' K) :=
    (continuousOn_localContinuousExtend g).comp hc.continuousOn (fun _ hz => hz)
  have hint (g : C(K, ℂ)) :
      IntegrableOn (fun z : X => localContinuousExtend g (c z)) (c ⁻¹' K) μ :=
    (hcont g).integrableOn_compact hL
  apply SupportAverage.tendsto_setAverage_ball_of_uniform μ hR
    ((hint (V q)).mono_set hpR) ((hcont (V q)).continuousAt hpL) hp
    (error := fun r => ‖(⨍ w in Metric.ball q r, V w ∂μ) - V q‖)
  · intro r _ hrR
    exact (hint _).mono_set ((Metric.ball_subset_ball hrR.le).trans hpR)
  · intro r _ hrR z hz
    have hzc : c z ∈ K := hpR ((Metric.ball_subset_ball hrR.le) hz)
    rw [localContinuousExtend_apply _ hzc, localContinuousExtend_apply _ hzc]
    exact (ContinuousMap.norm_coe_le_norm
      ((⨍ w in Metric.ball q r, V w ∂μ) - V q) ⟨c z, hzc⟩)
  · have hconst : Tendsto (fun _ : ℝ => V q) (𝓝[>] (0 : ℝ)) (𝓝 (V q)) :=
      tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hvavg.sub hconst).norm

/-- The actual modular measure version needs only interior locations in an
arbitrary compact upper-half-plane observation set. Its compact preimage
provides all local integrability certificates, including across modular seams. -/
theorem tendsto_modular_double_setAverage_ball
    {K : Set ℂ} [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    {V : UpperHalfPlane → C(K, ℂ)}
    (hV : ContinuousOn V (UpperHalfPlane.coe ⁻¹' K))
    {p q : UpperHalfPlane} (hp : p ∈ modularMeasure.support)
    (hq : q ∈ modularMeasure.support)
    (hpK : p ∈ interior (UpperHalfPlane.coe ⁻¹' K))
    (hqK : q ∈ interior (UpperHalfPlane.coe ⁻¹' K)) :
    letI : MetricSpace UpperHalfPlane :=
      UpperHalfPlane.isEmbedding_coe.comapMetricSpace UpperHalfPlane.coe
    Tendsto
      (fun r : ℝ => ⨍ z in Metric.ball p r,
        localContinuousExtend (⨍ w in Metric.ball q r, V w ∂modularMeasure)
          (z : ℂ) ∂modularMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 ((V q) ⟨(p : ℂ),
        interior_subset (s := UpperHalfPlane.coe ⁻¹' K) hpK⟩)) := by
  let : MetricSpace UpperHalfPlane :=
    UpperHalfPlane.isEmbedding_coe.comapMetricSpace UpperHalfPlane.coe
  change Tendsto _ _ _
  obtain ⟨Rp, hRp, hpR⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hpK)
  obtain ⟨Rq, hRq, hqR⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hqK)
  have hR : 0 < min Rp Rq := lt_min hRp hRq
  have h := tendsto_double_setAverage_ball modularMeasure UpperHalfPlane.continuous_coe
    (ModularGradient.isCompact_coe_preimage_of_subset_upperHalfPlane
      (isCompact_iff_compactSpace.mpr inferInstance) hKH)
    hV hp hq hR
    ((Metric.ball_subset_ball (min_le_left _ _)).trans hpR)
    ((Metric.ball_subset_ball (min_le_right _ _)).trans hqR)
  simpa only [localContinuousExtend_apply _
    (interior_subset (s := UpperHalfPlane.coe ⁻¹' K) hpK)] using h

end GapFamily.Analytic.SpatialPoint
