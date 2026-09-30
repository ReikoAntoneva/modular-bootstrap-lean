import GapFamily.Analytic.Poincare.Repair.PoincareCanonicalLocalRepair

/-! Concrete physical input data for the proved canonical local repair. -/

noncomputable section
namespace GapFamily.Construction

open Set MeasureTheory
open GapFamily.Analytic PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier
open scoped MatrixGroups

/-- A bounded signed input supported below its repair cutoff, with zero
ordinary signed mass in each active spin. The repair itself is canonical. -/
structure CanonicalRepairDatum where
  cutoffB : ℝ
  cutoff_one : 1 ≤ cutoffB
  input : ℤ → SignedMeasure ℝ
  physicalSupport : ∀ J ∈ lowBandSpinSet cutoffB,
    ∀ᵐ E ∂(input J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * cutoffB
  masszero : ∀ J ∈ lowBandSpinSet cutoffB, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(input J)) = 0
  inside : ∀ J ∈ lowBandSpinSet cutoffB, ∀ᵐ E ∂(input J).variation, E < cutoffB

namespace CanonicalRepairDatum

/-- The literal finite physical spin band of this input. -/
def active (D : CanonicalRepairDatum) : Finset ℤ := lowBandSpinSet D.cutoffB

/-- The actual inverse-and-anchor repair input already constructed analytically. -/
def repairInput (D : CanonicalRepairDatum) : ℤ → SignedMeasure ℝ :=
  canonicalLocalRepairInput D.input D.cutoffB D.cutoff_one D.physicalSupport

/-- The literal canonical corrected Poincaré seed. -/
def seed (D : CanonicalRepairDatum) : UpperHalfPlane → ℂ :=
  canonicalLocalRepairSeed D.input D.cutoffB D.cutoff_one D.physicalSupport

/-- The actual thermal output signed measure in one output spin. -/
def thermalOutput (D : CanonicalRepairDatum) (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  correctedThermalFiniteOutputMeasure D.active D.repairInput j t

theorem seed_smul (D : CanonicalRepairDatum) (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    D.seed (g • τ) = D.seed τ :=
  canonicalLocalRepairSeed_smul D.input D.cutoffB D.cutoff_one D.physicalSupport τ g

theorem repairInput_physicalSupport (D : CanonicalRepairDatum) :
    ∀ J ∈ D.active, ∀ᵐ E ∂(D.repairInput J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * D.cutoffB :=
  canonicalLocalRepairInput_physicalSupport D.input D.cutoffB D.cutoff_one D.physicalSupport

theorem repairInput_threshold_eq_zero (D : CanonicalRepairDatum) :
    finiteSignedThresholdMass D.active D.repairInput = 0 :=
  canonicalLocalRepairInput_threshold_eq_zero D.input D.cutoffB D.cutoff_one
    D.physicalSupport D.masszero

theorem hasSum_seed_output (D : CanonicalRepairDatum) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (D.thermalOutput j (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x)
      (D.seed (rowPoint y hy x)) :=
  hasSum_canonicalLocalRepairSeed_output D.input D.cutoffB D.cutoff_one
    D.physicalSupport y hy x

theorem thermalOutput_restrict_below_cutoff (D : CanonicalRepairDatum)
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (D.thermalOutput j t).restrict (Iio D.cutoffB) =
      if j ∈ D.active then thermalSignedInputMeasure (D.input j) t else 0 :=
  canonicalLocalRepairOutput_eq_input_below_cutoff D.input D.cutoffB D.cutoff_one
    D.physicalSupport D.masszero D.inside j ht

theorem thermalOutput_singleton (D : CanonicalRepairDatum) (j : ℤ)
    {t : ℝ} (ht : 0 < t) (e : ℝ) :
    D.thermalOutput j t {e} =
      if j ∈ D.active then Real.exp (-t * e) * D.input j {e} else 0 :=
  canonicalLocalRepairOutput_singleton D.input D.cutoffB D.cutoff_one
    D.physicalSupport D.masszero j ht e

theorem thermalOutput_preserves_vacuum (D : CanonicalRepairDatum)
    (V : SignedMeasure ℝ) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (V + D.thermalOutput j t).restrict (Iio (0 : ℝ)) = V.restrict (Iio (0 : ℝ)) :=
  canonicalLocalRepairOutput_preserves_vacuum D.input D.cutoffB D.cutoff_one
    D.physicalSupport V j ht

theorem summable_thermalOutput_totalVariation (D : CanonicalRepairDatum)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => (D.thermalOutput j t).variation.real univ) :=
  summable_correctedThermalFiniteOutputMeasure_totalVariation D.active D.repairInput
    (3 * D.cutoffB) D.repairInput_physicalSupport ht

theorem continuous_seed (D : CanonicalRepairDatum) : Continuous D.seed :=
  continuous_correctedSeedSuperposition D.active D.repairInput
    (3 * D.cutoffB) D.repairInput_physicalSupport

end CanonicalRepairDatum
end GapFamily.Construction
