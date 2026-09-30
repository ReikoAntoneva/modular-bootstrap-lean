import GapFamily.Construction.PermanentSpectrumRemainderBudget
import GapFamily.Construction.PermanentSpectrumRemainderSigned
import GapFamily.Construction.PermanentSpectrumRemainderDensity

/-! Complete slot corrections are summable from the actual thermal variation
of their signed residuals and the actual exterior density allowance. -/

noncomputable section
namespace GapFamily.Construction
open Set MeasureTheory Real
open scoped UpperHalfPlane
open Analytic

/-- The permitted exterior error is dominated by the same positive reference
envelope that controls the remaining continuum. -/
theorem exterior_error_le_tailEnvelopeNumerator (a E : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (hj : |(j : ℝ)| ≤ E) :
    exp (7 * sqrt (a * E)) ≤ tailEnvelopeNumerator a E j := by
  dsimp [tailEnvelopeNumerator]
  exact le_add_of_nonneg_left (vacuumLeading_nonneg a E j ha hj)

theorem slot_exterior_le_tailEnvelopeNumerator (a T : ℝ) (m : ℕ)
    (q : ℤ → ℝ → ℝ) (ha : 100 ≤ a)
    (hq : ∀ j : ℤ, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ Layer.slotBudget m * exp (7 * sqrt (a * E))) :
    ∀ j : ℤ, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ Layer.slotBudget m * tailEnvelopeNumerator a E j := by
  intro j
  filter_upwards [hq j, ae_restrict_mem measurableSet_Ici] with E hqE hE
  exact hqE.trans (mul_le_mul_of_nonneg_left
    (exterior_error_le_tailEnvelopeNumerator a E j (by linarith)
      ((le_max_right _ _).trans hE)) (by dsimp [Layer.slotBudget]; positivity))

/-- The exact slot allowance controls the absolute all-slot series of the
ordinary exterior Fourier-Laplace values. -/
theorem summable_norm_slotExteriorDensity (a T : ℝ)
    (q : (Σ m : ℕ, Layer.Slot m) → ℤ → ℝ → ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T)
    (hq : ∀ p j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q p j E| ≤ Layer.slotBudget p.1 * exp (7 * sqrt (a * E))) (τ : ℍ) :
    Summable (fun p => ‖tailDensityPointValue T (q p) τ‖) := by
  apply summable_norm_slotExterior _
    (sqrt τ.im * ∑' j : ℤ,
      ∫ E, exp (-(2 * π * τ.im) * E) ∂tailEnvelopeMeasure a T j)
  intro p
  have h := norm_tailDensityPointValue_le a T (Layer.slotBudget p.1) (q p) ha hT
    (slot_exterior_le_tailEnvelopeNumerator a T p.1 (q p) ha (hq p)) τ
  convert h using 1
  ring

/-- Every complete correction has genuine integral pieces and their entire
series converges absolutely. The decomposition is the actual C2 output
identity; it does not require the direct or exterior pieces to be modular. -/
theorem completeSlotCorrection_integrable_and_norm_summable
    (a T : ℝ) (ν : (Σ m : ℕ, Layer.Slot m) → SignedMeasure ℝ)
    (J : (Σ m : ℕ, Layer.Slot m) → ℤ)
    (q : (Σ m : ℕ, Layer.Slot m) → ℤ → ℝ → ℝ)
    (complete : (Σ m : ℕ, Layer.Slot m) → ℂ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) (τ : ℍ)
    (hm : ∀ p j, AEStronglyMeasurable (q p j)
      ((referenceMeasure j).restrict (Ici (max T |(j : ℝ)|))))
    (hq : ∀ p j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q p j E| ≤ Layer.slotBudget p.1 * exp (7 * sqrt (a * E)))
    (hthermal : ∀ p, Integrable (fun E => exp (-2 * π * τ.im * E)) (ν p).variation)
    (hsum : Summable (fun p => ∫ E, exp (-2 * π * τ.im * E) ∂(ν p).variation))
    (hcomplete : ∀ p, complete p = signedPointSeedHalf (ν p) (J p) τ +
      tailDensityPointValue T (q p) τ) :
    (∀ p, (ν p).Integrable (fun E => pointSeed E (J p) (1 / 2) τ)) ∧
    (∀ p j, IntegrableOn (fun E => exp (-(2 * π * τ.im) * E) * q p j E)
      (Ici (max T |(j : ℝ)|)) (referenceMeasure j)) ∧
    Summable (fun p => ‖complete p‖) := by
  refine ⟨fun p => signedIntegrable_pointSeed_half (ν p) (J p) τ (hthermal p), ?_, ?_⟩
  · intro p j
    exact integrable_tailDensityThermalRow a T (Layer.slotBudget p.1) (q p) j ha hT
      (by positivity) (hm p j)
      (slot_exterior_le_tailEnvelopeNumerator a T p.1 (q p) ha (hq p) j)
  · exact summable_norm_completeCorrection complete _ _ hcomplete
      (signedPointSeedHalf_norm_summable ν J τ hthermal hsum)
      (summable_norm_slotExteriorDensity a T q ha hT hq τ)

end GapFamily.Construction
