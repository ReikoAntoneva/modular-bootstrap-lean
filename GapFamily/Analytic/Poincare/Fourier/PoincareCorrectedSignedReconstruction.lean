import GapFamily.Analytic.Poincare.Fourier.PoincareCorrectedSignedOutput
import GapFamily.Analytic.Poincare.Fourier.PoincareSignedFourierCircle

/-! Complete Fourier reconstruction of the actual corrected finite signed seed.
Bounded physical input support supplies all coefficient summability and ordinary
kernel integrability. The conclusion identifies the actual modular function
with its direct input, scalar threshold, and corrected reference-density output.
-/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory PoincareFourier PoincareEnergyContinuation
open scoped Topology

/-- A bounded physical signed row has uniform reconstruction on the unit circle. -/
theorem hasSum_correctedRowCircle
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    HasSum (fun j : ℤ => correctedRowFourierCoefficient y hy ν j J •
      (fourier j : C(AddCircle (1 : ℝ), ℂ))) (correctedRowCircle y hy ν J B hs) :=
  hasSum_correctedRowCircle_of_summable y hy ν J B hs
    (summable_correctedRowSeed_fourier ν J B hs y hy)

/-- The actual corrected signed row is recovered at every horizontal point. -/
theorem hasSum_correctedRowSeed_row
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (x : ℝ) :
    HasSum (fun j : ℤ => correctedRowFourierCoefficient y hy ν j J * cuspFourierMode j x)
      (correctedRowSeed ν J (rowPoint y hy x)) :=
  hasSum_correctedRowSeed_row_of_summable y hy ν J B hs
    (summable_correctedRowSeed_fourier ν J B hs y hy) x

/-- The complete ordinary reference-density output reconstructs the actual
corrected row, with no Fourier or Fubini premise beyond bounded physical input. -/
theorem hasSum_correctedRowSeed_full_laplace
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (x : ℝ) :
    HasSum (fun j : ℤ =>
      ((if j = J then (Real.sqrt y : ℂ) *
        (∫ᵛ E : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (E : ℂ)) ∂<•ν)
        else 0) +
      (if j = 0 then (Real.sqrt y : ℂ) *
        PoincareScalarFourier.scalarThresholdCoefficient J * (ν univ : ℂ) else 0) +
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          correctedSignedRowResponse ν J j e ∂referenceMeasure j) * cuspFourierMode j x)
      (correctedRowSeed ν J (rowPoint y hy x)) := by
  convert (hasSum_correctedRowSeed_row y hy ν J B hs x) using 1
  ext j
  unfold correctedRowFourierCoefficient
  rw [correctedRowSeed_fourier_eq_full_laplace ν J j B hs y hy]

/-- Every bounded physical finite signed family has uniform circle reconstruction. -/
theorem hasSum_correctedFiniteCircle
    (y : ℝ) (hy : 0 < y) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    HasSum (fun j : ℤ => correctedFiniteFourierCoefficient y hy S ν j •
      (fourier j : C(AddCircle (1 : ℝ), ℂ))) (correctedFiniteCircle y hy S ν B hs) :=
  hasSum_correctedFiniteCircle_of_summable y hy S ν B hs
    (summable_correctedSeedSuperposition_fourier S ν B hs y hy)

/-- The actual finite corrected signed seed is reconstructed at every point. -/
theorem hasSum_correctedSeedSuperposition_row
    (y : ℝ) (hy : 0 < y) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (x : ℝ) :
    HasSum (fun j : ℤ => correctedFiniteFourierCoefficient y hy S ν j * cuspFourierMode j x)
      (correctedSeedSuperposition S ν (rowPoint y hy x)) :=
  hasSum_correctedSeedSuperposition_row_of_summable y hy S ν B hs
    (summable_correctedSeedSuperposition_fourier S ν B hs y hy) x

/-- Complete ordinary Fourier–Laplace output of the actual corrected finite
signed modular seed. The only input assumption is bounded physical support. -/
theorem hasSum_correctedSeedSuperposition_full_laplace
    (y : ℝ) (hy : 0 < y) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (x : ℝ) :
    HasSum (fun j : ℤ =>
      (∑ J ∈ S, ((if j = J then (Real.sqrt y : ℂ) *
        (∫ᵛ E : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (E : ℂ)) ∂<•(ν J))
        else 0) +
      (if j = 0 then (Real.sqrt y : ℂ) *
        PoincareScalarFourier.scalarThresholdCoefficient J * ((ν J) univ : ℂ) else 0) +
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          correctedSignedRowResponse (ν J) J j e ∂referenceMeasure j)) * cuspFourierMode j x)
      (correctedSeedSuperposition S ν (rowPoint y hy x)) := by
  convert (hasSum_correctedSeedSuperposition_row y hy S ν B hs x) using 1
  ext j
  unfold correctedFiniteFourierCoefficient
  rw [correctedSeedSuperposition_fourier_eq_full_laplace S ν j B hs y hy]

end GapFamily.Analytic.PoincareEnergyFourier
