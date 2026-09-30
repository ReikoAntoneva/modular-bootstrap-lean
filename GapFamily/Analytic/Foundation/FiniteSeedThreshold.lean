import GapFamily.Analytic.Foundation.ThresholdCoefficientBound
import GapFamily.Analytic.Poincare.Fourier.PoincareThermalOutputMeasure

/-! The actual scalar threshold mass of finitely many ordinary signed input rows. -/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory
open scoped Classical BigOperators

/-- The real coefficient of the origin Dirac measure produced by a finite signed input. -/
def finiteSignedThresholdMass (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) : ℝ :=
  ∑ J ∈ S, (PoincareScalarFourier.scalarThresholdCoefficient J).re * ν J univ

/-- The real threshold mass is exactly the original complex coefficient sum. -/
theorem finiteSignedThresholdMass_complex (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) :
    (finiteSignedThresholdMass S ν : ℂ) =
      ∑ J ∈ S, PoincareScalarFourier.scalarThresholdCoefficient J * (ν J univ : ℂ) := by
  simp only [finiteSignedThresholdMass, Complex.ofReal_sum, Complex.ofReal_mul,
    PoincareScalarFourier.scalarThresholdCoefficient_re_coe]

@[simp] theorem finiteSignedThresholdMass_zero (S : Finset ℤ) :
    finiteSignedThresholdMass S 0 = 0 := by
  simp [finiteSignedThresholdMass]

@[simp] theorem finiteSignedThresholdMass_singleton (J : ℤ) (ν : ℤ → SignedMeasure ℝ) :
    finiteSignedThresholdMass {J} ν =
      (PoincareScalarFourier.scalarThresholdCoefficient J).re * ν J univ := by
  simp [finiteSignedThresholdMass]

/-- Addition is ordinary addition of the actual input signed measures. -/
theorem finiteSignedThresholdMass_add (S : Finset ℤ) (ν μ : ℤ → SignedMeasure ℝ) :
    finiteSignedThresholdMass S (ν + μ) =
      finiteSignedThresholdMass S ν + finiteSignedThresholdMass S μ := by
  simp [finiteSignedThresholdMass, mul_add, Finset.sum_add_distrib]

/-- Real scaling acts on the signed input measures themselves. -/
theorem finiteSignedThresholdMass_smul (S : Finset ℤ) (r : ℝ) (ν : ℤ → SignedMeasure ℝ) :
    finiteSignedThresholdMass S (r • ν) = r * finiteSignedThresholdMass S ν := by
  simp only [finiteSignedThresholdMass, Pi.smul_apply, _root_.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  ring

theorem finiteSignedThresholdMass_sub (S : Finset ℤ) (ν μ : ℤ → SignedMeasure ℝ) :
    finiteSignedThresholdMass S (ν - μ) =
      finiteSignedThresholdMass S ν - finiteSignedThresholdMass S μ := by
  simp [finiteSignedThresholdMass, mul_sub, Finset.sum_sub_distrib]

/-- The finite signed-family threshold coefficient is a real linear functional. -/
def finiteSignedThresholdMassLinearMap (S : Finset ℤ) : (ℤ → SignedMeasure ℝ) →ₗ[ℝ] ℝ where
  toFun := finiteSignedThresholdMass S
  map_add' := finiteSignedThresholdMass_add S
  map_smul' r ν := finiteSignedThresholdMass_smul S r ν

@[simp] theorem finiteSignedThresholdMassLinearMap_apply (S : Finset ℤ)
    (ν : ℤ → SignedMeasure ℝ) :
    finiteSignedThresholdMassLinearMap S ν = finiteSignedThresholdMass S ν := rfl

/-- Zeroth signed mass cancellation in each input row removes the complete threshold atom. -/
theorem finiteSignedThresholdMass_eq_zero_of_row_mass_eq_zero
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (hν : ∀ J ∈ S, ν J univ = 0) :
    finiteSignedThresholdMass S ν = 0 := by
  apply Finset.sum_eq_zero
  intro J hJ
  rw [hν J hJ, mul_zero]

/-- The zeroth ordinary signed moment is exactly the signed mass of the whole input row. -/
theorem signedIntegral_one_eq_mass (ν : SignedMeasure ℝ) :
    (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•ν) = ν univ := by
  let := signedMeasure_isFiniteMeasure_variation ν
  simp

/-- Ordinary zeroth-moment cancellation suffices; no positivity or scalar atom hypothesis is needed. -/
theorem finiteSignedThresholdMass_eq_zero_of_zeroth_moment
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (hν : ∀ J ∈ S, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0) :
    finiteSignedThresholdMass S ν = 0 := by
  apply finiteSignedThresholdMass_eq_zero_of_row_mass_eq_zero S ν
  intro J hJ
  simpa only [signedIntegral_one_eq_mass] using hν J hJ

/-- Adding a rowwise mass-cancelling repair preserves the actual threshold coefficient. -/
theorem finiteSignedThresholdMass_add_of_row_mass_eq_zero
    (S : Finset ℤ) (ν μ : ℤ → SignedMeasure ℝ) (hμ : ∀ J ∈ S, μ J univ = 0) :
    finiteSignedThresholdMass S (ν + μ) = finiteSignedThresholdMass S ν := by
  rw [finiteSignedThresholdMass_add,
    finiteSignedThresholdMass_eq_zero_of_row_mass_eq_zero S μ hμ, add_zero]

/-- The threshold contribution of a finite signed seed is one literal scalar atom. -/
theorem correctedThermalFiniteOutputMeasure_eq (S : Finset ℤ)
    (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (t : ℝ) :
    correctedThermalFiniteOutputMeasure S ν j t =
      (if j ∈ S then thermalSignedInputMeasure (ν j) t else 0) +
      (∑ J ∈ S, correctedThermalContinuumMeasure (ν J) J j t) +
      (if j = 0 then VectorMeasure.dirac (0 : ℝ) (finiteSignedThresholdMass S ν)
        else 0) := by
  ext s hs
  simp only [correctedThermalFiniteOutputMeasure, correctedThermalRowOutputMeasure,
    Finset.sum_add_distrib, _root_.add_apply]
  by_cases hj : j ∈ S <;> by_cases h0 : j = 0 <;> by_cases hs0 : (0 : ℝ) ∈ s <;>
    simp [hj, h0, hs0, hs, finiteSignedThresholdMass, VectorMeasure.dirac]

/-- Finite signed superposition creates no atoms beyond the input and scalar threshold. -/
theorem correctedThermalFiniteOutputMeasure_singleton (S : Finset ℤ)
    (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalFiniteOutputMeasure S ν j t {e} =
      (if j ∈ S then Real.exp (-t * e) * ν j {e} else 0) +
      (if j = 0 ∧ e = 0 then finiteSignedThresholdMass S ν else 0) := by
  rw [correctedThermalFiniteOutputMeasure_apply]
  trans ∑ J ∈ S,
    ((if j = J then Real.exp (-t * e) * ν J {e} else 0) +
      (if j = 0 ∧ e = 0 then
        (PoincareScalarFourier.scalarThresholdCoefficient J).re * ν J univ else 0))
  · apply Finset.sum_congr rfl
    intro J hJ
    exact correctedThermalRowOutputMeasure_singleton (ν J) J j B (hs J hJ) ht e
  simp [Finset.sum_add_distrib, finiteSignedThresholdMass, Finset.sum_ite_irrel]

end GapFamily.Analytic
