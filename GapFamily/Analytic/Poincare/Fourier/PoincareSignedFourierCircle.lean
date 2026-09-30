import GapFamily.Analytic.Poincare.Fourier.PoincareCorrectedSignedFourier
import GapFamily.Analytic.Poincare.Fourier.PoincareGeneralFourierCircle

/-! Circle reconstruction of the actual corrected finite signed seed. The
functions on the circle are literal periodic quotients of the global modular
seeds, and their coefficients are their ordinary horizontal Fourier integrals.
-/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory PoincareFourier PoincareEnergyContinuation
open scoped Topology

/-- The corrected signed row is periodic by its actual modular invariance. -/
theorem periodic_correctedRowSeed_row (y : ℝ) (hy : 0 < y)
    (ν : SignedMeasure ℝ) (J : ℤ) :
    Function.Periodic (fun x => correctedRowSeed ν J (rowPoint y hy x)) 1 := by
  intro x
  change correctedRowSeed ν J (rowPoint y hy (x + 1)) =
    correctedRowSeed ν J (rowPoint y hy x)
  rw [rowPoint_add_one, correctedRowSeed_smul]

/-- The ordinary horizontal Fourier coefficient of the actual corrected row. -/
def correctedRowFourierCoefficient (y : ℝ) (hy : 0 < y)
    (ν : SignedMeasure ℝ) (j J : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
    correctedRowSeed ν J (rowPoint y hy x)

/-- This actual coefficient is the ordinary signed integral of the corrected
point-seed coefficients. -/
theorem correctedRowFourierCoefficient_eq_signedIntegral
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (j J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    correctedRowFourierCoefficient y hy ν j J =
      ∫ᵛ E : ℝ, correctedPointFourierCoefficient y hy E j J ∂<•ν :=
  correctedRowSeed_fourier y hy ν j J B hs

/-- The actual corrected signed row as a continuous function on the unit circle. -/
def correctedRowCircle (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    C(AddCircle (1 : ℝ), ℂ) where
  toFun := (periodic_correctedRowSeed_row y hy ν J).lift
  continuous_toFun := continuous_coinduced_dom.mpr
    ((continuous_correctedRowSeed ν J B hs).comp (continuous_rowPoint y hy))

/-- Every real coordinate evaluates to the literal corrected signed seed. -/
@[simp] theorem correctedRowCircle_coe (y : ℝ) (hy : 0 < y)
    (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (x : ℝ) :
    correctedRowCircle y hy ν J B hs (x : AddCircle (1 : ℝ)) =
      correctedRowSeed ν J (rowPoint y hy x) :=
  (periodic_correctedRowSeed_row y hy ν J).lift_coe x

/-- Circle Fourier extraction is the actual ordinary horizontal coefficient. -/
theorem fourierCoeff_correctedRowCircle (y : ℝ) (hy : 0 < y)
    (ν : SignedMeasure ℝ) (j J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    fourierCoeff (correctedRowCircle y hy ν J B hs) j =
      correctedRowFourierCoefficient y hy ν j J := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [one_div, inv_one, one_smul, zero_add, smul_eq_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [fourier_coe_eq_cuspFourierMode, correctedRowCircle_coe]

/-- Summability of the actual row coefficients gives uniform circle reconstruction. -/
theorem hasSum_correctedRowCircle_of_summable
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (hcoeff : Summable (fun j : ℤ => correctedRowFourierCoefficient y hy ν j J)) :
    HasSum (fun j : ℤ => correctedRowFourierCoefficient y hy ν j J •
      (fourier j : C(AddCircle (1 : ℝ), ℂ))) (correctedRowCircle y hy ν J B hs) := by
  have hc : Summable (fourierCoeff (correctedRowCircle y hy ν J B hs)) :=
    hcoeff.congr (fun j => (fourierCoeff_correctedRowCircle y hy ν j J B hs).symm)
  simpa only [fourierCoeff_correctedRowCircle] using hasSum_fourier_series_of_summable hc

/-- The actual signed row is reconstructed at every real coordinate. -/
theorem hasSum_correctedRowSeed_row_of_summable
    (y : ℝ) (hy : 0 < y) (ν : SignedMeasure ℝ) (J : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (hcoeff : Summable (fun j : ℤ => correctedRowFourierCoefficient y hy ν j J)) (x : ℝ) :
    HasSum (fun j : ℤ => correctedRowFourierCoefficient y hy ν j J * cuspFourierMode j x)
      (correctedRowSeed ν J (rowPoint y hy x)) := by
  have hc : Summable (fourierCoeff (correctedRowCircle y hy ν J B hs)) :=
    hcoeff.congr (fun j => (fourierCoeff_correctedRowCircle y hy ν j J B hs).symm)
  simpa only [fourierCoeff_correctedRowCircle, smul_eq_mul,
    fourier_coe_eq_cuspFourierMode, correctedRowCircle_coe] using
    has_pointwise_sum_fourier_series_of_summable hc (x : AddCircle (1 : ℝ))

/-- The actual finite corrected signed seed is periodic on every horizontal row. -/
theorem periodic_correctedSeedSuperposition_row (y : ℝ) (hy : 0 < y)
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) :
    Function.Periodic (fun x => correctedSeedSuperposition S ν (rowPoint y hy x)) 1 := by
  intro x
  change correctedSeedSuperposition S ν (rowPoint y hy (x + 1)) =
    correctedSeedSuperposition S ν (rowPoint y hy x)
  rw [rowPoint_add_one, correctedSeedSuperposition_smul]

/-- The ordinary Fourier coefficient of the actual finite corrected seed. -/
def correctedFiniteFourierCoefficient (y : ℝ) (hy : 0 < y)
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
    correctedSeedSuperposition S ν (rowPoint y hy x)

/-- Finite coefficient extraction is the actual finite signed integral. -/
theorem correctedFiniteFourierCoefficient_eq_sum_signedIntegral
    (y : ℝ) (hy : 0 < y) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    correctedFiniteFourierCoefficient y hy S ν j =
      ∑ J ∈ S, ∫ᵛ E : ℝ, correctedPointFourierCoefficient y hy E j J ∂<•(ν J) :=
  correctedSeedSuperposition_fourier y hy S ν j B hs

/-- The finite actual coefficient is the finite sum of its actual row coefficients. -/
theorem correctedFiniteFourierCoefficient_eq_sum_row
    (y : ℝ) (hy : 0 < y) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    correctedFiniteFourierCoefficient y hy S ν j =
      ∑ J ∈ S, correctedRowFourierCoefficient y hy (ν J) j J := by
  rw [correctedFiniteFourierCoefficient_eq_sum_signedIntegral y hy S ν j B hs]
  exact Finset.sum_congr rfl fun J hJ =>
    (correctedRowFourierCoefficient_eq_signedIntegral y hy (ν J) j J B (hs J hJ)).symm

/-- The actual finite corrected signed seed on the unit circle. -/
def correctedFiniteCircle (y : ℝ) (hy : 0 < y)
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    C(AddCircle (1 : ℝ), ℂ) where
  toFun := (periodic_correctedSeedSuperposition_row y hy S ν).lift
  continuous_toFun := continuous_coinduced_dom.mpr
    ((continuous_correctedSeedSuperposition S ν B hs).comp (continuous_rowPoint y hy))

/-- Every real coordinate evaluates to the actual finite corrected signed seed. -/
@[simp] theorem correctedFiniteCircle_coe (y : ℝ) (hy : 0 < y)
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) (x : ℝ) :
    correctedFiniteCircle y hy S ν B hs (x : AddCircle (1 : ℝ)) =
      correctedSeedSuperposition S ν (rowPoint y hy x) :=
  (periodic_correctedSeedSuperposition_row y hy S ν).lift_coe x

/-- Circle extraction agrees with the actual finite horizontal Fourier integral. -/
theorem fourierCoeff_correctedFiniteCircle (y : ℝ) (hy : 0 < y)
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B) :
    fourierCoeff (correctedFiniteCircle y hy S ν B hs) j =
      correctedFiniteFourierCoefficient y hy S ν j := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [one_div, inv_one, one_smul, zero_add, smul_eq_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [fourier_coe_eq_cuspFourierMode, correctedFiniteCircle_coe]

/-- Absolute summability of the actual finite coefficients reconstructs the
actual circle function in the continuous-function norm. -/
theorem hasSum_correctedFiniteCircle_of_summable
    (y : ℝ) (hy : 0 < y) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (hcoeff : Summable (fun j : ℤ => correctedFiniteFourierCoefficient y hy S ν j)) :
    HasSum (fun j : ℤ => correctedFiniteFourierCoefficient y hy S ν j •
      (fourier j : C(AddCircle (1 : ℝ), ℂ))) (correctedFiniteCircle y hy S ν B hs) := by
  have hc : Summable (fourierCoeff (correctedFiniteCircle y hy S ν B hs)) :=
    hcoeff.congr (fun j => (fourierCoeff_correctedFiniteCircle y hy S ν j B hs).symm)
  simpa only [fourierCoeff_correctedFiniteCircle] using hasSum_fourier_series_of_summable hc

/-- Summable actual coefficients recover the finite corrected seed at every
horizontal point; no almost-everywhere spatial conclusion is substituted. -/
theorem hasSum_correctedSeedSuperposition_row_of_summable
    (y : ℝ) (hy : 0 < y) (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (hcoeff : Summable (fun j : ℤ => correctedFiniteFourierCoefficient y hy S ν j)) (x : ℝ) :
    HasSum (fun j : ℤ => correctedFiniteFourierCoefficient y hy S ν j * cuspFourierMode j x)
      (correctedSeedSuperposition S ν (rowPoint y hy x)) := by
  have hc : Summable (fourierCoeff (correctedFiniteCircle y hy S ν B hs)) :=
    hcoeff.congr (fun j => (fourierCoeff_correctedFiniteCircle y hy S ν j B hs).symm)
  simpa only [fourierCoeff_correctedFiniteCircle, smul_eq_mul,
    fourier_coe_eq_cuspFourierMode, correctedFiniteCircle_coe] using
    has_pointwise_sum_fourier_series_of_summable hc (x : AddCircle (1 : ℝ))

end GapFamily.Analytic.PoincareEnergyFourier
