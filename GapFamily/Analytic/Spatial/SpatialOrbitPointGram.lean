import GapFamily.Analytic.Spatial.SpatialOrbitAverageGramIdentity
import GapFamily.Analytic.Spatial.SpatialOrbitDoubleAverageLimit
import GapFamily.Analytic.Spatial.SpatialOrbitCorrectedResponseLimit
import GapFamily.Analytic.Spatial.SpatialOrbitFiniteEvaluation
import GapFamily.Analytic.Spatial.SpatialOrbitThresholdModular
import GapFamily.Analytic.Modular.ModularMeasureSupport
import GapFamily.Analytic.Foundation.FiniteKernelPosSemidef

/-! Finite point positivity of the actual corrected compact response, obtained
from ordinary shrinking modular-measure averages of the positive operator. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane ModularGradient Dirichlet
open UpperWeightedCoherence
open scoped Topology ComplexOrder MatrixGroups

/-- At physical real parameters, every finite matrix observed inside a compact
upper-half-plane chart is positive at points in the modular-measure support. -/
theorem spatialOrbitCorrectedResponse_posSemidef_of_support
    {K : Set ℂ} [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (D : Evaluation (1 / 4) (by norm_num) K)
    {ι : Type*} [Fintype ι] (p : ι → UpperHalfPlane)
    (hp : ∀ i, p i ∈ modularMeasure.support)
    (hpK : ∀ i, p i ∈ interior (UpperHalfPlane.coe ⁻¹' K))
    (s : ℝ) (hs : 1 / 2 < s) (hne : s ≠ 1)
    (hn : ‖(s : ℂ) - 1 / 2‖ < D.radius) :
    Matrix.PosSemidef (fun i j =>
      spatialOrbitCorrectedEvaluation (spatialOrbitCompactResponse D) (s : ℂ) (p j)
        ⟨(p i : ℂ), interior_subset (s := UpperHalfPlane.coe ⁻¹' K) (hpK i)⟩) := by
  let : MetricSpace UpperHalfPlane :=
    UpperHalfPlane.isEmbedding_coe.comapMetricSpace UpperHalfPlane.coe
  have hballs : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ i, Metric.ball (p i) r ⊆ UpperHalfPlane.coe ⁻¹' K := by
    rw [Filter.eventually_all]
    intro i
    obtain ⟨R, hR, hRi⟩ := Metric.mem_nhds_iff.mp
      (mem_interior_iff_mem_nhds.mp (hpK i))
    filter_upwards [(eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with r hr
    exact (Metric.ball_subset_ball hr.le).trans hRi
  apply PositiveOperatorGram.posSemidef_of_tendsto_entries
    (l := 𝓝[>] (0 : ℝ))
    (fun r : ℝ => spatialOrbitAverageGram s hs (fun i => Metric.ball (p i) r)
      (fun _ => Metric.isOpen_ball.measurableSet))
  · exact Eventually.of_forall fun _ => spatialOrbitAverageGram_posSemidef s hs _ _
  · intro i j
    have hV : ContinuousOn
        (spatialOrbitCorrectedEvaluation (spatialOrbitCompactResponse D) (s : ℂ))
        (UpperHalfPlane.coe ⁻¹' K) :=
      ((continuous_spatialOrbitCompactResponse_source D (s : ℂ)
        (by simpa only [Complex.ofReal_re] using (by linarith : 0 < s))).sub
        continuous_const).continuousOn
    have hlim := tendsto_modular_double_setAverage_ball hKH hV (hp i) (hp j)
      (hpK i) (hpK j)
    apply hlim.congr'
    filter_upwards [hballs] with r hr
    exact (spatialOrbitAverageGram_entry_eq_response_average hKH D s hs hne hn
      (fun i => Metric.ball (p i) r) (fun _ => Metric.isOpen_ball.measurableSet) hr i j).symm

/-- The endpoint compact response is the canonical corrected spatial kernel.
The parameter limit is taken only after finite point matrices are proved positive. -/
theorem spatialThresholdCorrectedKernel_posSemidef_of_support_compact
    {K : Set ℂ} [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (D : Evaluation (1 / 4) (by norm_num) K)
    {ι : Type*} [Fintype ι] (p : ι → UpperHalfPlane)
    (hp : ∀ i, p i ∈ modularMeasure.support)
    (hpK : ∀ i, p i ∈ interior (UpperHalfPlane.coe ⁻¹' K)) :
    Matrix.PosSemidef (fun i j => spatialThresholdCorrectedKernel (p i) (p j)) := by
  apply PositiveOperatorGram.posSemidef_of_tendsto_entries
    (l := 𝓝[>] (1 / 2 : ℝ))
    (fun s : ℝ => fun i j =>
      spatialOrbitCorrectedEvaluation (spatialOrbitCompactResponse D) (s : ℂ) (p j)
        ⟨(p i : ℂ), interior_subset (s := UpperHalfPlane.coe ⁻¹' K) (hpK i)⟩)
  · filter_upwards [eventually_spatialOrbit_physical_half D] with s hs
    exact spatialOrbitCorrectedResponse_posSemidef_of_support hKH D p hp hpK
      s hs.1 hs.2.1 hs.2.2
  · intro i j
    exact (tendsto_spatialOrbitCorrectedResponse_half_apply D (p i) (p j)
      (interior_subset (s := UpperHalfPlane.coe ⁻¹' K) (hpK i))).mono_left nhdsWithin_le_nhds

/-- Finite point positivity on the full closed modular fundamental domain,
including every seam, follows from support positivity of the actual measure. -/
theorem spatialThresholdCorrectedKernel_posSemidef_of_support
    {ι : Type*} [Fintype ι] (p : ι → UpperHalfPlane)
    (hp : ∀ i, p i ∈ modularMeasure.support) :
    Matrix.PosSemidef (fun i j => spatialThresholdCorrectedKernel (p i) (p j)) := by
  obtain ⟨K, hK, hKH, hpK⟩ := exists_compact_upperNeighborhood_of_finite p
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨D⟩ := nonempty_evaluation K hKH (by norm_num : (0 : ℝ) < 1 / 4)
  apply spatialThresholdCorrectedKernel_posSemidef_of_support_compact hKH D p hp
  intro i
  apply mem_interior_iff_mem_nhds.mpr
  exact UpperHalfPlane.continuous_coe.continuousAt
    (mem_interior_iff_mem_nhds.mp (hpK i))

/-- Every finite Gram matrix of the canonical threshold kernel with its exact
constant correction `+6` is positive semidefinite on the entire upper half-plane. -/
theorem spatialThresholdCorrectedKernel_posSemidef
    {ι : Type*} [Fintype ι] (p : ι → UpperHalfPlane) :
    Matrix.PosSemidef (fun i j => spatialThresholdCorrectedKernel (p i) (p j)) := by
  classical
  choose γ hγ using fun i => ModularGroup.exists_smul_mem_fd (p i)
  have hpos := spatialThresholdCorrectedKernel_posSemidef_of_support
    (fun i => γ i • p i) (fun i => by rw [modularMeasure_support]; exact hγ i)
  simpa only [spatialThresholdCorrectedKernel_modular] using hpos

/-- Unrestricted matrix formulation: every finitely supported spatial
quadratic form is nonnegative, ready for genuine Fourier and height averages. -/
theorem spatialThresholdCorrectedKernel_matrix_posSemidef :
    Matrix.PosSemidef spatialThresholdCorrectedKernel := by
  apply FiniteKernelPosSemidef.posSemidef_of_finite_gram
  intro ι _ p
  exact spatialThresholdCorrectedKernel_posSemidef p

end GapFamily.Analytic.SpatialPoint
