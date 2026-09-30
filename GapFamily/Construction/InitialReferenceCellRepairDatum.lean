import GapFamily.Construction.InitialReferenceCellThermal
import GapFamily.Construction.CanonicalRepairDatum

/-! The actual initial-cell residual supplies the canonical modular repair datum. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GapFamily.Construction
open Analytic PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier

namespace InitialReferenceCell

variable {J : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
  (cell : InitialReferenceCell J L U k q)

/-- A literal unit node witnesses that the closed initial cell is nonempty. -/
theorem left_le_right : L ≤ cell.right :=
  (cell.node_mem ⟨0, cell.count_pos⟩).1.trans (cell.node_mem ⟨0, cell.count_pos⟩).2

/-- The initial residual occupies exactly its prescribed input row. -/
def rowInput (j : ℤ) : SignedMeasure ℝ := if j = J then cell.residual else 0

@[simp] theorem rowInput_self : cell.rowInput J = cell.residual := by simp [rowInput]

@[simp] theorem rowInput_ne {j : ℤ} (h : j ≠ J) : cell.rowInput j = 0 := by
  simp [rowInput, h]

/-- A cutoff beyond the actual endpoint contains the initial cell's spin. -/
theorem input_spin_mem (B : ℝ) (hJ : |(J : ℝ)| ≤ L) (hcut : cell.right < B) :
    J ∈ lowBandSpinSet B := by
  rw [mem_lowBandSpinSet]
  exact (hJ.trans cell.left_le_right).trans_lt hcut

/-- The actual residual has the physical compact support required by repair. -/
theorem rowInput_physicalSupport (B : ℝ) (hB : 1 ≤ B)
    (hJ : |(J : ℝ)| ≤ L) (hcut : cell.right < B) :
    ∀ j ∈ lowBandSpinSet B, ∀ᵐ E ∂(cell.rowInput j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ 3 * B := by
  intro j _
  by_cases hj : j = J
  · subst j
    rw [rowInput_self]
    filter_upwards [cell.ae_mem_cell] with E hE
    exact ⟨hJ.trans hE.1, by linarith [hE.2]⟩
  · simp [rowInput_ne cell hj, VectorMeasure.variation_zero]

/-- Every input row is supported strictly below the repair cutoff. -/
theorem rowInput_inside (B : ℝ) (hcut : cell.right < B) :
    ∀ j ∈ lowBandSpinSet B, ∀ᵐ E ∂(cell.rowInput j).variation, E < B := by
  intro j _
  by_cases hj : j = J
  · subst j
    rw [rowInput_self]
    filter_upwards [cell.ae_mem_cell] with E hE
    exact hE.2.trans_lt hcut
  · simp [rowInput_ne cell hj, VectorMeasure.variation_zero]

/-- The actual matched signed mass supplies the zeroth moment in every row. -/
theorem rowInput_integral_one (B : ℝ) :
    ∀ j ∈ lowBandSpinSet B, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(cell.rowInput j)) = 0 := by
  intro j _
  by_cases hj : j = J
  · subst j
    rw [rowInput_self]
    rw [signedIntegral_one_eq_mass]
    exact cell.residual_mass
  · simp [rowInput_ne cell hj]

variable (B : ℝ) (hB : 1 ≤ B) (hJ : |(J : ℝ)| ≤ L) (hcut : cell.right < B)

/-- The canonical datum is formed from the literal initial-cell residual. -/
def repairDatum : CanonicalRepairDatum where
  cutoffB := B
  cutoff_one := hB
  input := cell.rowInput
  physicalSupport := cell.rowInput_physicalSupport B hB hJ hcut
  masszero := cell.rowInput_integral_one B
  inside := cell.rowInput_inside B hcut

/-- The actual inverse-and-anchor repair input of this initial cell. -/
def repairInput : ℤ → SignedMeasure ℝ := (cell.repairDatum B hB hJ hcut).repairInput

/-- The actual corrected Poincaré seed associated with the initial cell. -/
def repairSeed : UpperHalfPlane → ℂ := (cell.repairDatum B hB hJ hcut).seed

/-- The complete ordinary thermal output of the initial-cell repair. -/
def repairOutput : ℤ → ℝ → SignedMeasure ℝ :=
  (cell.repairDatum B hB hJ hcut).thermalOutput

@[simp] theorem repairDatum_cutoffB : (cell.repairDatum B hB hJ hcut).cutoffB = B := rfl
@[simp] theorem repairDatum_input : (cell.repairDatum B hB hJ hcut).input = cell.rowInput := rfl
@[simp] theorem repairDatum_repairInput :
    (cell.repairDatum B hB hJ hcut).repairInput = cell.repairInput B hB hJ hcut := rfl
@[simp] theorem repairDatum_seed :
    (cell.repairDatum B hB hJ hcut).seed = cell.repairSeed B hB hJ hcut := rfl
@[simp] theorem repairDatum_thermalOutput :
    (cell.repairDatum B hB hJ hcut).thermalOutput = cell.repairOutput B hB hJ hcut := rfl

theorem repairInput_physicalSupport :
    ∀ j ∈ lowBandSpinSet B, ∀ᵐ E ∂(cell.repairInput B hB hJ hcut j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ 3 * B :=
  (cell.repairDatum B hB hJ hcut).repairInput_physicalSupport

theorem repairInput_threshold_eq_zero :
    finiteSignedThresholdMass (lowBandSpinSet B) (cell.repairInput B hB hJ hcut) = 0 :=
  (cell.repairDatum B hB hJ hcut).repairInput_threshold_eq_zero

theorem repairSeed_smul (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    cell.repairSeed B hB hJ hcut (g • τ) = cell.repairSeed B hB hJ hcut τ :=
  (cell.repairDatum B hB hJ hcut).seed_smul τ g

theorem hasSum_repairSeed_output (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (cell.repairOutput B hB hJ hcut j (2 * Real.pi * y) univ : ℂ) *
        cuspFourierMode j x)
      (cell.repairSeed B hB hJ hcut (rowPoint y hy x)) :=
  (cell.repairDatum B hB hJ hcut).hasSum_seed_output y hy x

/-- Below the cutoff the full modular response is exactly the thermal residual. -/
theorem repairOutput_below_cutoff (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (cell.repairOutput B hB hJ hcut j t).restrict (Iio B) =
      if j = J then thermalSignedInputMeasure cell.residual t else 0 := by
  change ((cell.repairDatum B hB hJ hcut).thermalOutput j t).restrict
    (Iio (cell.repairDatum B hB hJ hcut).cutoffB) = _
  rw [CanonicalRepairDatum.thermalOutput_restrict_below_cutoff _ j ht]
  by_cases hj : j = J
  · subst j
    simp [CanonicalRepairDatum.active, cell.input_spin_mem B hJ hcut]
  · simp [CanonicalRepairDatum.active, rowInput, hj, thermalSignedInputMeasure,
      VectorMeasure.withDensity_zero_vectorMeasure]

/-- The repair retains precisely the literal unit-node multiplicity. -/
theorem repairOutput_singleton (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    cell.repairOutput B hB hJ hcut j t {e} =
      if j = J then Real.exp (-t * e) *
        ∑ i : Fin cell.count, if cell.node i = e then (1 : ℝ) else 0
      else 0 := by
  change (cell.repairDatum B hB hJ hcut).thermalOutput j t {e} = _
  rw [CanonicalRepairDatum.thermalOutput_singleton _ j ht e]
  by_cases hj : j = J
  · subst j
    simp [CanonicalRepairDatum.active, cell.input_spin_mem B hJ hcut,
      cell.residual_singleton]
  · simp [CanonicalRepairDatum.active, rowInput, hj]

theorem repairOutput_preserves_vacuum (V : SignedMeasure ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (V + cell.repairOutput B hB hJ hcut j t).restrict (Iio (0 : ℝ)) =
      V.restrict (Iio (0 : ℝ)) :=
  (cell.repairDatum B hB hJ hcut).thermalOutput_preserves_vacuum V j ht

theorem summable_repairOutput_totalVariation {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => (cell.repairOutput B hB hJ hcut j t).variation.real univ) :=
  (cell.repairDatum B hB hJ hcut).summable_thermalOutput_totalVariation ht

theorem continuous_repairSeed : Continuous (cell.repairSeed B hB hJ hcut) :=
  (cell.repairDatum B hB hJ hcut).continuous_seed

end InitialReferenceCell
end GapFamily.Construction
