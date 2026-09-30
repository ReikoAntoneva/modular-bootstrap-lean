import GapFamily.Analytic.Spatial.SpatialOrbitAverageGram
import GapFamily.Analytic.Spatial.SpatialOrbitThresholdSourceAverage
import GapFamily.Analytic.Modular.ModularCompactEvaluationAE

/-! Actual positive spatial average matrices use the continuous corrected
kernel representatives, with ordinary modular-measure equality justified. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane ModularGradient Dirichlet
open UpperWeightedCoherence
open scoped Topology ComplexOrder

theorem spatialOrbitAverageGram_entry_eq_response_average
    {K : Set ℂ} [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (D : Evaluation (1 / 4) (by norm_num) K)
    (s : ℝ) (hs : 1 / 2 < s) (hne : s ≠ 1)
    (hn : ‖(s : ℂ) - 1 / 2‖ < D.radius)
    {ι : Type*} (S : ι → Set UpperHalfPlane) (hS : ∀ i, MeasurableSet (S i))
    (hSK : ∀ i, S i ⊆ UpperHalfPlane.coe ⁻¹' K) (i j : ι) :
    spatialOrbitAverageGram s hs S hS i j =
      ⨍ z in S i, localContinuousExtend
        (⨍ w in S j, spatialOrbitCorrectedEvaluation (spatialOrbitCompactResponse D)
          (s : ℂ) w ∂modularMeasure) (z : ℂ) ∂modularMeasure := by
  let f : ModularHilbert := L2NormalizedIndicator.vector modularMeasure (S j) (hS j)
  let L : Set UpperHalfPlane := UpperHalfPlane.coe ⁻¹' K
  have hL : IsCompact L := isCompact_coe_preimage_of_subset_upperHalfPlane
    (isCompact_iff_compactSpace.mpr inferInstance) hKH
  have hf : ∀ᵐ w ∂modularMeasure, w ∉ L → f w = 0 := by
    filter_upwards [L2NormalizedIndicator.vector_ae modularMeasure (S j) (hS j)] with w hw
    intro hnL
    rw [hw, Set.indicator_of_notMem]
    exact fun hwS => hnL (hSK j hwS)
  have havg := spatialOrbitCorrectedResponse_average_physical_of_compact_support
    D s hs hne hn f L hL hf
  rw [L2NormalizedIndicator.integral_vector_smul] at havg
  have hrep := laplacianUpperCompactRestriction_lift_modular_ae
    D.cutoff D.cutoff_smooth D.cutoff_compact D.cutoff_support
    D.region D.open_region D.one_region K D.compact_subset
    ⟨spatialOrbitMeanZeroContinuation s hs f,
      spatialOrbitMeanZeroContinuation_mem_laplacian_domain s hs f⟩
  rw [spatialOrbitAverageGram_entry, setAverage_eq, setAverage_eq]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (hS i), ae_restrict_of_ae hrep] with z hz hze
  have he := hze (hSK i hz)
  rw [← he]
  change localContinuousExtend
      (spatialOrbitCompactGraphRestriction D (gradientLift laplacian
        ⟨spatialOrbitMeanZeroContinuation s hs f,
          spatialOrbitMeanZeroContinuation_mem_laplacian_domain s hs f⟩)) (z : ℂ) = _
  rw [← havg]

end GapFamily.Analytic.SpatialPoint
