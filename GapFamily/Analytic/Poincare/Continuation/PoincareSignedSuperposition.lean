import GapFamily.Analytic.Poincare.Seed.PoincareEnergyIdentification
import GapFamily.Analytic.Foundation.SignedMomentIntegral

/-! Actual ordinary signed superposition of a bounded physical input row. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set Filter MeasureTheory UpperHalfPlane ModularGradient PoincareCanonical
open scoped Topology MatrixGroups

/-- The actual continued seed is strongly measurable in the real input energy. -/
theorem aestronglyMeasurable_generalThresholdSeed_realEnergy
    (J : ℤ) (τ : UpperHalfPlane) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun E : ℝ => generalThresholdSeed E J τ) μ := by
  have hc : Continuous (fun E : ℂ => generalThresholdSeed E J τ) :=
    continuous_iff_continuousAt.mpr fun E =>
      (analyticAt_generalThresholdSeed_energy E J τ).continuousAt
  exact (hc.comp Complex.continuous_ofReal).aestronglyMeasurable

/-- Ordinary signed integration of the actual scalar seed, against one input row. -/
def rowSeedSuperposition (ν : SignedMeasure ℝ) (J : ℤ) (τ : UpperHalfPlane) : ℂ :=
  ∫ᵛ E : ℝ, generalThresholdSeed E J τ ∂<•ν

/-- Compact observation bounds dominate every bounded physical input row. -/
theorem exists_generalThresholdSeed_row_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ) (ν : SignedMeasure ℝ) (J : ℤ),
      (∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) →
      ∀ (τ : UpperHalfPlane), (τ : ℂ) ∈ K →
        ∀ᵐ E : ℝ ∂ν.variation, ‖generalThresholdSeed E J τ‖ ≤ C * (1 + B) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := generalThresholdSeed_physical_bound K hKH
  refine ⟨C, hC, ?_⟩
  intro B ν J hs τ hτ
  filter_upwards [hs] with E hE
  have hE0 : 0 ≤ E := (abs_nonneg (J : ℝ)).trans hE.1
  have hm := mul_self_le_mul_self (show 0 ≤ 1 + E by linarith)
    (show 1 + E ≤ 1 + B by linarith [hE.2])
  exact (hb E J hE.1 τ hτ).trans
    (mul_le_mul_of_nonneg_left (by nlinarith) hC.le)

/-- A bounded physical signed row has an ordinary integrable continued seed
at every upper-half-plane point, with respect to its actual variation. -/
theorem rowSeedSuperposition_integrable (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (τ : UpperHalfPlane) :
    ν.Integrable (fun E : ℝ => generalThresholdSeed E J τ) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  obtain ⟨C, _hC, hb⟩ := exists_generalThresholdSeed_row_bound
    ({(τ : ℂ)} : Set ℂ) (singleton_subset_upper τ)
  exact (integrable_const (C * (1 + B) ^ 2)).mono'
    (aestronglyMeasurable_generalThresholdSeed_realEnergy J τ ν.variation)
    (hb B ν J hs τ (mem_singleton _))

/-- The ordinary signed superposition retains actual modular invariance. -/
theorem rowSeedSuperposition_smul (ν : SignedMeasure ℝ) (J : ℤ)
    (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    rowSeedSuperposition ν J (g • τ) = rowSeedSuperposition ν J τ := by
  unfold rowSeedSuperposition
  simp only [generalThresholdSeed_smul]

/-- Ordinary dominated continuity applies on a genuine compact neighborhood
of each observation point, including modular seams. -/
theorem continuous_rowSeedSuperposition (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    Continuous (rowSeedSuperposition ν J) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  apply continuous_iff_continuousAt.mpr
  intro τ
  obtain ⟨K, U, hK, _hreg, hτK, _hU, hKU, _hUc, hUH⟩ :=
    exists_regularCompact_upperNeighborhood (K := ({(τ : ℂ)} : Set ℂ))
      isCompact_singleton (singleton_subset_upper τ)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hKH : K ⊆ upperHalfPlaneSet := hKU.trans (subset_closure.trans hUH)
  obtain ⟨C, _hC, hb⟩ := exists_generalThresholdSeed_row_bound K hKH
  have hKn : K ∈ 𝓝 (τ : ℂ) := mem_of_superset
    (isOpen_interior.mem_nhds (hτK (mem_singleton _))) interior_subset
  have hnear : ∀ᶠ ξ : UpperHalfPlane in 𝓝 τ, (ξ : ℂ) ∈ K :=
    UpperHalfPlane.continuous_coe.continuousAt.eventually hKn
  apply VectorMeasure.continuousAt_of_dominated
    (μ := ν) (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip)
    (bound := fun _ : ℝ => C * (1 + B) ^ 2)
  · exact Eventually.of_forall fun ξ =>
      aestronglyMeasurable_generalThresholdSeed_realEnergy J ξ ν.variation
  · filter_upwards [hnear] with ξ hξ
    exact hb B ν J hs ξ hξ
  · exact integrable_const _
  · exact Eventually.of_forall fun E => (continuous_generalThresholdSeed E J).continuousAt

/-- One compact constant controls the superposition by the ordinary total
variation mass and the physical input energy cutoff. -/
theorem rowSeedSuperposition_compact_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ) (ν : SignedMeasure ℝ) (J : ℤ),
      (∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) →
      ∀ (τ : UpperHalfPlane), (τ : ℂ) ∈ K →
        ‖rowSeedSuperposition ν J τ‖ ≤ ν.variation.real univ * (C * (1 + B) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_generalThresholdSeed_row_bound K hKH
  refine ⟨C, hC, ?_⟩
  intro B ν J hs τ hτ
  let := signedMeasure_isFiniteMeasure_variation ν
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip) (hb B ν J hs τ hτ)
  simpa only [rowSeedSuperposition, ContinuousLinearMap.opNorm_flip,
    ContinuousLinearMap.opNorm_lsmul, mul_one, one_mul, mul_comm] using h

end GapFamily.Analytic.PoincareEnergyContinuation
