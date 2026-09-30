import GapFamily.Construction.FixedCutoffMarkerTransfer
import GapFamily.Analytic.Poincare.Repair.PoincareLocalRepairThreshold

/-!
# Exact modular transfer of a scalar marker

The repair cutoff is `2B`, so removal of the old marker at `B` occurs in the
interior. The input never places an atom at zero; for a prescribed zero gap,
the normalized threshold of the actual modular correction supplies it.
-/

noncomputable section

open MeasureTheory Set UpperHalfPlane
open scoped Classical BigOperators MatrixGroups

namespace GapFamily.Construction

open Analytic PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier

/-- A common compact input band for every prescribed marker in `[0,B]`. -/
theorem fixedCutoffMarkerTransfer_repairSupport (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) :
    ∀ J ∈ lowBandSpinSet (2 * B),
      ∀ᵐ E ∂(fixedCutoffMarkerTransfer B δ J).variation,
        |(J : ℝ)| ≤ E ∧ E ≤ 3 * (2 * B) := by
  intro J _
  exact (fixedCutoffMarkerTransfer_physicalSupport B δ hδ hδB J).mono
    (fun _ h => ⟨h.1, by linarith [h.2]⟩)

/-- The exact repaired signed input, defined by the proved canonical inverse. -/
def fixedCutoffMarkerRepairInput (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) : ℤ → SignedMeasure ℝ :=
  canonicalLocalRepairInput (fixedCutoffMarkerTransfer B δ) (2 * B) (by linarith)
    (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB)

theorem fixedCutoffMarkerRepairInput_physicalSupport (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) :
    ∀ J ∈ lowBandSpinSet (2 * B),
      ∀ᵐ E ∂(fixedCutoffMarkerRepairInput B δ hB hδ hδB J).variation,
        |(J : ℝ)| ≤ E ∧ E ≤ 3 * (2 * B) :=
  canonicalLocalRepairInput_physicalSupport (fixedCutoffMarkerTransfer B δ) (2 * B)
    (by linarith) (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB)

/-- The transfer is an actual modular Poincaré superposition. -/
def fixedCutoffMarkerRepairSeed (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) (τ : UpperHalfPlane) : ℂ :=
  correctedSeedSuperposition (lowBandSpinSet (2 * B))
    (fixedCutoffMarkerRepairInput B δ hB hδ hδB) τ

theorem fixedCutoffMarkerRepairSeed_smul (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    fixedCutoffMarkerRepairSeed B δ hB hδ hδB (g • τ) =
      fixedCutoffMarkerRepairSeed B δ hB hδ hδB τ :=
  correctedSeedSuperposition_smul (lowBandSpinSet (2 * B)) _ τ g

theorem fixedCutoffMarkerRepairInput_threshold (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) :
    finiteSignedThresholdMass (lowBandSpinSet (2 * B))
      (fixedCutoffMarkerRepairInput B δ hB hδ hδB) = if δ = 0 then 1 else 0 := by
  rw [fixedCutoffMarkerRepairInput, canonicalLocalRepairInput_threshold]
  exact fixedCutoffMarkerTransfer_threshold _ (by simp; linarith) B δ hδ

/-- Complete ordinary output of the same actual modular correction. -/
def fixedCutoffMarkerRepairThermalMeasure (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  correctedThermalFiniteOutputMeasure (lowBandSpinSet (2 * B))
    (fixedCutoffMarkerRepairInput B δ hB hδ hδB) j t

/-- The exact atom formula also covers the threshold endpoint. -/
theorem fixedCutoffMarkerRepairThermalMeasure_singleton (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    fixedCutoffMarkerRepairThermalMeasure B δ hB hδ hδB j t {e} =
      (if j = 0 ∧ e = δ then Real.exp (-t * e) else 0) -
        (if j = 0 ∧ e = B then Real.exp (-t * e) else 0) := by
  unfold fixedCutoffMarkerRepairThermalMeasure fixedCutoffMarkerRepairInput
  rw [canonicalLocalRepairOutput_singleton_with_threshold
      (fixedCutoffMarkerTransfer B δ) (2 * B) (by linarith)
      (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB) j ht e,
    fixedCutoffMarkerTransfer_singleton,
    fixedCutoffMarkerTransfer_threshold _ (by simp; linarith) B δ hδ]
  by_cases hj : j = 0
  · subst j
    have hzero : (0 : ℤ) ∈ lowBandSpinSet (2 * B) := by simp; linarith
    by_cases hδ0 : δ = 0
    · subst δ
      by_cases he : e = 0 <;> by_cases heB : e = B <;>
        simp_all
    · have hpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
      by_cases he : e = δ <;> by_cases heB : e = B <;>
        simp_all
  · simp [hj]

theorem hasSum_fixedCutoffMarkerRepairSeed_output (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (fixedCutoffMarkerRepairThermalMeasure B δ hB hδ hδB j
        (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x)
      (fixedCutoffMarkerRepairSeed B δ hB hδ hδB (rowPoint y hy x)) :=
  hasSum_correctedSeedSuperposition_thermalOutputMeasure (lowBandSpinSet (2 * B)) _
    (3 * (2 * B)) (fixedCutoffMarkerRepairInput_physicalSupport B δ hB hδ hδB) y hy x

end GapFamily.Construction
