import GapFamily.Analytic.Poincare.Fourier.PoincareCorrectedSignedFourier

/-!
# Linearity of the actual corrected signed seed

Addition and subtraction use ordinary integrability of the point seed and the
scalar square-root moment under each physical input row. Real homogeneity
follows from the actual signed-measure integral.
-/

noncomputable section

namespace GapFamily.Analytic.PoincareEnergyContinuation

open Set Filter MeasureTheory UpperHalfPlane

/-- Addition of two bounded physical signed rows adds their actual corrected
modular seeds, including the scalar moment. -/
theorem correctedRowSeed_add (ν μ : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (hμ : ∀ᵐ E ∂μ.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (τ : UpperHalfPlane) :
    correctedRowSeed (ν + μ) J τ = correctedRowSeed ν J τ + correctedRowSeed μ J τ := by
  have hiν : ν.Integrable (fun E : ℝ => (Real.sqrt E : ℂ)) :=
    (signedIntegrable_sqrt_of_bounded_above ν B (hν.mono fun _ h => h.2)).ofReal
  have hiμ : μ.Integrable (fun E : ℝ => (Real.sqrt E : ℂ)) :=
    (signedIntegrable_sqrt_of_bounded_above μ B (hμ.mono fun _ h => h.2)).ofReal
  simp only [correctedRowSeed]
  rw [rowSeedSuperposition_add ν μ J B hν hμ τ]
  by_cases hJ : J = 0
  · rw [ite_eq_left hJ, ite_eq_left hJ, ite_eq_left hJ,
      VectorMeasure.integral_add_vectorMeasure hiν hiμ]
    ring
  · simp [hJ]

/-- Subtraction of bounded physical rows is literal subtraction of their
actual corrected modular functions. -/
theorem correctedRowSeed_sub (ν μ : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (hμ : ∀ᵐ E ∂μ.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (τ : UpperHalfPlane) :
    correctedRowSeed (ν - μ) J τ = correctedRowSeed ν J τ - correctedRowSeed μ J τ := by
  have hiν : ν.Integrable (fun E : ℝ => (Real.sqrt E : ℂ)) :=
    (signedIntegrable_sqrt_of_bounded_above ν B (hν.mono fun _ h => h.2)).ofReal
  have hiμ : μ.Integrable (fun E : ℝ => (Real.sqrt E : ℂ)) :=
    (signedIntegrable_sqrt_of_bounded_above μ B (hμ.mono fun _ h => h.2)).ofReal
  simp only [correctedRowSeed, rowSeedSuperposition]
  rw [VectorMeasure.integral_sub_vectorMeasure
    (rowSeedSuperposition_integrable ν J B hν τ) (rowSeedSuperposition_integrable μ J B hμ τ)]
  by_cases hJ : J = 0
  · rw [ite_eq_left hJ, ite_eq_left hJ, ite_eq_left hJ,
      VectorMeasure.integral_sub_vectorMeasure hiν hiμ]
    ring
  · simp [hJ]

/-- Real multiplication of the actual signed input multiplies the corrected
seed by the same real number. -/
theorem correctedRowSeed_smul_input (a : ℝ) (ν : SignedMeasure ℝ) (J : ℤ)
    (τ : UpperHalfPlane) :
    correctedRowSeed (a • ν) J τ = a • correctedRowSeed ν J τ := by
  simp only [correctedRowSeed, rowSeedSuperposition, VectorMeasure.integral_smul_vectorMeasure]
  by_cases hJ : J = 0
  · simp only [ite_eq_left hJ, Complex.real_smul]
    ring
  · simp [hJ]

/-- The zero signed input contributes exactly the zero corrected seed. -/
@[simp] theorem correctedRowSeed_zero (J : ℤ) (τ : UpperHalfPlane) :
    correctedRowSeed 0 J τ = 0 := by
  simp [correctedRowSeed, rowSeedSuperposition]

/-- Finite signed input addition is addition of the actual corrected seeds. -/
theorem correctedSeedSuperposition_add (S : Finset ℤ)
    (ν μ : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (τ : UpperHalfPlane) :
    correctedSeedSuperposition S (fun J => ν J + μ J) τ =
      correctedSeedSuperposition S ν τ + correctedSeedSuperposition S μ τ := by
  simp only [correctedSeedSuperposition, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun J hJ => correctedRowSeed_add (ν J) (μ J) J B (hν J hJ) (hμ J hJ) τ

/-- Finite signed input subtraction is subtraction of the actual corrected seeds. -/
theorem correctedSeedSuperposition_sub (S : Finset ℤ)
    (ν μ : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (τ : UpperHalfPlane) :
    correctedSeedSuperposition S (fun J => ν J - μ J) τ =
      correctedSeedSuperposition S ν τ - correctedSeedSuperposition S μ τ := by
  simp only [correctedSeedSuperposition, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun J hJ => correctedRowSeed_sub (ν J) (μ J) J B (hν J hJ) (hμ J hJ) τ

/-- Real input multiplication commutes with the actual finite corrected seed. -/
theorem correctedSeedSuperposition_smul_input (S : Finset ℤ) (a : ℝ)
    (ν : ℤ → SignedMeasure ℝ) (τ : UpperHalfPlane) :
    correctedSeedSuperposition S (fun J => a • ν J) τ = a • correctedSeedSuperposition S ν τ := by
  simp only [correctedSeedSuperposition, correctedRowSeed_smul_input, Finset.smul_sum]

/-- The actual finite corrected seed of zero input is zero. -/
@[simp] theorem correctedSeedSuperposition_zero (S : Finset ℤ) (τ : UpperHalfPlane) :
    correctedSeedSuperposition S (fun _ => 0) τ = 0 := by
  simp [correctedSeedSuperposition]

end GapFamily.Analytic.PoincareEnergyContinuation
