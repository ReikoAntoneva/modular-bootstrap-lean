import GapFamily.Analytic.Poincare.Continuation.PoincareSignedSuperposition

/-! Finite physical spin rows and their exact ordinary signed superposition. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology MatrixGroups

/-- An input atom contributes exactly its constructed continued seed. -/
theorem rowSeedSuperposition_dirac (E : ℝ) (J : ℤ) (τ : UpperHalfPlane) :
    rowSeedSuperposition (Measure.dirac E).toSignedMeasure J τ =
      generalThresholdSeed E J τ := by
  simp [rowSeedSuperposition, VectorMeasure.integral_toSignedMeasure]

/-- Addition of ordinary signed rows is justified by their actual integrability. -/
theorem rowSeedSuperposition_add (ν μ : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (hμ : ∀ᵐ E ∂μ.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (τ : UpperHalfPlane) :
    rowSeedSuperposition (ν + μ) J τ =
      rowSeedSuperposition ν J τ + rowSeedSuperposition μ J τ := by
  exact VectorMeasure.integral_add_vectorMeasure
    (rowSeedSuperposition_integrable ν J B hν τ)
    (rowSeedSuperposition_integrable μ J B hμ τ)

/-- The actual finite-spin superposition of ordinary signed input rows. -/
def finiteSeedSuperposition (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  ∑ J ∈ S, rowSeedSuperposition (ν J) J τ

/-- The same finite ordinary superposition is modular on the whole upper half-plane. -/
theorem finiteSeedSuperposition_smul (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    finiteSeedSuperposition S ν (g • τ) = finiteSeedSuperposition S ν τ := by
  simp only [finiteSeedSuperposition, rowSeedSuperposition_smul]

/-- Every bounded physical finite-spin signed input has a continuous modular output. -/
theorem continuous_finiteSeedSuperposition (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (B : ℝ) (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    Continuous (finiteSeedSuperposition S ν) := by
  exact continuous_finsetSum S fun J hJ => continuous_rowSeedSuperposition (ν J) J B (hs J hJ)

/-- The bound depends on the actual sum of input variation masses, without a
separate cardinality factor for the finite spin set. -/
theorem finiteSeedSuperposition_compact_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ),
      (∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) →
      ∀ (τ : UpperHalfPlane), (τ : ℂ) ∈ K →
        ‖finiteSeedSuperposition S ν τ‖ ≤
          (∑ J ∈ S, (ν J).variation.real univ) * (C * (1 + B) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := rowSeedSuperposition_compact_bound K hKH
  refine ⟨C, hC, ?_⟩
  intro S ν B hs τ hτ
  calc
    _ ≤ ∑ J ∈ S, ‖rowSeedSuperposition (ν J) J τ‖ := norm_sum_le _ _
    _ ≤ ∑ J ∈ S, (ν J).variation.real univ * (C * (1 + B) ^ 2) :=
      Finset.sum_le_sum fun J hJ => hb B (ν J) J (hs J hJ) τ hτ
    _ = _ := (Finset.sum_mul _ _ _).symm

end GapFamily.Analytic.PoincareEnergyContinuation
