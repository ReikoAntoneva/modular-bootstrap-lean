import GapFamily.Construction.TailCellAtomic
import GapFamily.Analytic.Poincare.Repair.PoincareCanonicalLocalRepair

/-! The canonical modular local repair applied to an actual moment-matched tail cell. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GapFamily.Construction
open Analytic PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier

namespace TailCell

variable {J : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ} (cell : TailCell J L k q)

/-- The actual cell residual occupies exactly its prescribed input row. -/
def rowInput (j : ℤ) : SignedMeasure ℝ := if j = J then cell.residual else 0

@[simp]theorem rowInput_self : cell.rowInput J = cell.residual := by simp [rowInput]

@[simp]theorem rowInput_ne {j : ℤ} (h : j ≠ J) : cell.rowInput j = 0 := by
  simp [rowInput, h]

/-- The cell's input row belongs to the physical band of every cutoff beyond the cell. -/
theorem input_spin_mem (B : ℝ) (hJ : |(J : ℝ)| ≤ L) (hcut : cell.right < B) :
    J ∈ lowBandSpinSet B := by
  rw [mem_lowBandSpinSet]
  have := cell.right_mem.1
  linarith

/-- The actual residual meets the compact physical support hypothesis of local repair. -/
theorem rowInput_physicalSupport (B : ℝ) (hB : 1 ≤ B)
    (hJ : |(J : ℝ)| ≤ L) (hcut : cell.right < B) :
    ∀ j ∈ lowBandSpinSet B, ∀ᵐ E ∂(cell.rowInput j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ 3 * B := by
  intro j _
  by_cases hj : j = J
  · subst j
    rw [rowInput_self]
    filter_upwards [cell.residual_ae_mem] with E hE
    exact ⟨hJ.trans hE.1, by linarith [hE.2]⟩
  · simp [rowInput_ne cell hj, VectorMeasure.variation_zero]

/-- Every input row lies strictly below the chosen cutoff. -/
theorem rowInput_inside (B : ℝ) (hcut : cell.right < B) :
    ∀ j ∈ lowBandSpinSet B, ∀ᵐ E ∂(cell.rowInput j).variation, E < B := by
  intro j _
  by_cases hj : j = J
  · subst j
    rw [rowInput_self]
    filter_upwards [cell.residual_ae_mem] with E hE
    exact hE.2.trans_lt hcut
  · simp [rowInput_ne cell hj, VectorMeasure.variation_zero]

/-- The literal zeroth signed moment vanishes in every input row. -/
theorem rowInput_integral_one (B : ℝ) :
    ∀ j ∈ lowBandSpinSet B, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(cell.rowInput j)) = 0 := by
  intro j _
  by_cases hj : j = J
  · subst j
    rw [rowInput_self]
    simpa only [Polynomial.eval_one, TailCell.residual] using
      (cell.moment (1 : Polynomial ℝ) (by simp)).2
  · simp [rowInput_ne cell hj]

variable (B : ℝ) (hB : 1 ≤ B) (hJ : |(J : ℝ)| ≤ L) (hcut : cell.right < B)

/-- The actual inverse-and-anchor repair input of this cell. -/
def repairInput : ℤ → SignedMeasure ℝ :=
  canonicalLocalRepairInput cell.rowInput B hB
    (cell.rowInput_physicalSupport B hB hJ hcut)

/-- The literal corrected Poincaré superposition repairing this cell. -/
def repairSeed (τ : UpperHalfPlane) : ℂ :=
  canonicalLocalRepairSeed cell.rowInput B hB
    (cell.rowInput_physicalSupport B hB hJ hcut) τ

/-- The complete ordinary thermal output of the actual cell repair. -/
def repairOutput (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  correctedThermalFiniteOutputMeasure (lowBandSpinSet B) (cell.repairInput B hB hJ hcut) j t

theorem repairInput_physicalSupport :
    ∀ j ∈ lowBandSpinSet B, ∀ᵐ E ∂(cell.repairInput B hB hJ hcut j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ 3 * B :=
  canonicalLocalRepairInput_physicalSupport cell.rowInput B hB
    (cell.rowInput_physicalSupport B hB hJ hcut)

theorem repairInput_threshold_eq_zero :
    finiteSignedThresholdMass (lowBandSpinSet B) (cell.repairInput B hB hJ hcut) = 0 :=
  canonicalLocalRepairInput_threshold_eq_zero cell.rowInput B hB
    (cell.rowInput_physicalSupport B hB hJ hcut) (cell.rowInput_integral_one B)

theorem repairSeed_smul (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    cell.repairSeed B hB hJ hcut (g • τ) = cell.repairSeed B hB hJ hcut τ :=
  canonicalLocalRepairSeed_smul cell.rowInput B hB
    (cell.rowInput_physicalSupport B hB hJ hcut) τ g

theorem hasSum_repairSeed_output (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (cell.repairOutput B hB hJ hcut j (2 * Real.pi * y) univ : ℂ) *
        cuspFourierMode j x)
      (cell.repairSeed B hB hJ hcut (rowPoint y hy x)) :=
  hasSum_canonicalLocalRepairSeed_output cell.rowInput B hB
    (cell.rowInput_physicalSupport B hB hJ hcut) y hy x

/-- Below the cutoff the complete modular response is exactly the single-row
thermal cell residual, with no contribution in any other spin. -/
theorem repairOutput_below_cutoff (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (cell.repairOutput B hB hJ hcut j t).restrict (Iio B) =
      if j = J then thermalSignedInputMeasure cell.residual t else 0 := by
  change (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
    (canonicalLocalRepairInput cell.rowInput B hB _) j t).restrict _ = _
  rw [canonicalLocalRepairOutput_eq_input_below_cutoff _ _ _ _
    (cell.rowInput_integral_one B) (cell.rowInput_inside B hcut)]
  · by_cases hj : j = J
    · subst j
      simp [cell.input_spin_mem B hJ hcut]
    · simp [hj, thermalSignedInputMeasure,
        VectorMeasure.withDensity_zero_vectorMeasure]
  · exact ht

/-- The modular repair retains exactly the cell's unit atoms, including their
multiplicity; the repair and its continuum introduce no further atom. -/
theorem repairOutput_singleton (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    cell.repairOutput B hB hJ hcut j t {e} =
      if j = J then Real.exp (-t * e) *
        ∑ i : Fin cell.count, if cell.node i = e then (1 : ℝ) else 0
      else 0 := by
  change correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
    (canonicalLocalRepairInput cell.rowInput B hB _) j t {e} = _
  rw [canonicalLocalRepairOutput_singleton _ _ _ _ (cell.rowInput_integral_one B) j ht e]
  by_cases hj : j = J
  · subst j
    simp [cell.input_spin_mem B hJ hcut, cell.residual_singleton]
  · simp [hj]

/-- Adding this repair preserves the complete negative-energy measure. -/
theorem repairOutput_preserves_vacuum (V : SignedMeasure ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (V + cell.repairOutput B hB hJ hcut j t).restrict (Iio (0 : ℝ)) =
      V.restrict (Iio (0 : ℝ)) :=
  canonicalLocalRepairOutput_preserves_vacuum cell.rowInput B hB
    (cell.rowInput_physicalSupport B hB hJ hcut) V j ht

end TailCell
end GapFamily.Construction
