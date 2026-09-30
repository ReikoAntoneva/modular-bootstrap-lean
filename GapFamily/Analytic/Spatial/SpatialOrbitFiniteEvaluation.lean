import GapFamily.Analytic.Spatial.SpatialOrbitCorrectedResponseLimit

/-! One actual compact evaluator for every finite family of upper points, and
the eventual real physical conditions needed for the threshold matrix limit. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter UpperHalfPlane ModularGradient UpperWeightedCoherence
open scoped Topology

/-- Every finite upper-point configuration lies in the interior of one compact
set that remains entirely in the upper half-plane. -/
theorem exists_compact_upperNeighborhood_of_finite
    {ι : Type*} [Fintype ι] (p : ι → UpperHalfPlane) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ upperHalfPlaneSet ∧
      ∀ i : ι, (p i : ℂ) ∈ interior K := by
  let P : Set ℂ := Set.range (fun i => (p i : ℂ))
  have hP : IsCompact P := (Set.finite_range (fun i => (p i : ℂ))).isCompact
  have hPH : P ⊆ upperHalfPlaneSet := by
    rintro z ⟨i, rfl⟩
    exact (p i).im_pos
  obtain ⟨K, U, hK, _hreg, hPK, _hU, hKU, _hUc, hUH⟩ :=
    exists_regularCompact_upperNeighborhood hP hPH
  exact ⟨K, hK, hKU.trans (subset_closure.trans hUH),
    fun i => hPK ⟨i, rfl⟩⟩

/-- The compact observation data and its positive radius are constructed for
the whole finite configuration at once. -/
theorem exists_spatialOrbitFiniteEvaluation
    {ι : Type*} [Fintype ι] (p : ι → UpperHalfPlane) :
    ∃ (K : Set ℂ) (hK : IsCompact K)
      (D : @Evaluation (1 / 4) (by norm_num) K (isCompact_iff_compactSpace.mp hK)),
      K ⊆ upperHalfPlaneSet ∧ (∀ i : ι, (p i : ℂ) ∈ interior K) ∧
        0 < @Evaluation.radius (1 / 4) (by norm_num) K
          (isCompact_iff_compactSpace.mp hK) D := by
  obtain ⟨K, hK, hKH, hpK⟩ := exists_compact_upperNeighborhood_of_finite p
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨D⟩ := nonempty_evaluation K hKH (by norm_num : (0 : ℝ) < 1 / 4)
  exact ⟨K, hK, D, hKH, hpK, D.radius_pos⟩

/-- On the right-hand neighborhood of one half, the parameter satisfies every
physical-side condition required by the corrected source-average identity. -/
theorem eventually_spatialOrbit_physical_half
    {K : Set ℂ} [CompactSpace K] (D : Evaluation (1 / 4) (by norm_num) K) :
    ∀ᶠ s : ℝ in 𝓝[>] (1 / 2),
      1 / 2 < s ∧ s ≠ 1 ∧ ‖(s : ℂ) - 1 / 2‖ < D.radius := by
  have hlt : ∀ᶠ s : ℝ in 𝓝 (1 / 2), s < 1 :=
    (isOpen_lt continuous_id continuous_const).mem_nhds (by norm_num)
  have hn : ∀ᶠ s : ℝ in 𝓝 (1 / 2), ‖(s : ℂ) - 1 / 2‖ < D.radius :=
    (isOpen_lt (Complex.continuous_ofReal.sub continuous_const).norm
      continuous_const).mem_nhds (by simpa using D.radius_pos)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hlt,
    mem_nhdsWithin_of_mem_nhds hn] with s hs hs1 hnorm
  exact ⟨hs, ne_of_lt hs1, hnorm⟩

end GapFamily.Analytic.SpatialPoint
