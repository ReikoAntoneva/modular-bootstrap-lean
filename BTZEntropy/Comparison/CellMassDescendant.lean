import BTZEntropy.Comparison.CellMassEnvelope
import BTZEntropy.Comparison.ReferenceBoltzmann
import BTZEntropy.Comparison.InitialPacketPartition
import BTZEntropy.Descendant

/-!
# The true cell envelope with every descendant level

The positive envelope bounds the absolute density mass of actual repair
cells, including their signed spin-opening pieces. Summing the two exact
partition multiplicities preserves the exponent `4 * π * sqrt (a * X)`.
The remaining thermal factor is independent of the charge and node choice.
-/

noncomputable section

open Real
open scoped BigOperators

namespace BTZEntropy.Comparison

set_option autoImplicit false

/-- The mass estimate retains a fixed Boltzmann loss even when the removed
energy exceeds the available energy, since that contribution then vanishes. -/
theorem cellEnvelopeMass_sub_le_boltzmann {a T X U q : ℝ}
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hX : 0 < X) (hU : 0 < U)
    (hXU : X ≤ U * a) (hq : 0 ≤ q) :
    cellEnvelopeMass a T (X - q) ≤
      (9 * (1 + X) ^ 2 * exp (4 * Real.pi * sqrt (a * X))) *
        exp (-(2 * Real.pi / sqrt U) * q) := by
  by_cases hqX : q ≤ X
  · have hp : 9 * (1 + (X - q)) ^ 2 ≤ 9 * (1 + X) ^ 2 := by
      gcongr
      linarith
    calc
      _ ≤ 9 * (1 + (X - q)) ^ 2 * exp (4 * Real.pi * sqrt (a * (X - q))) :=
        cellEnvelopeMass_le ha hT (sub_nonneg.mpr hqX)
      _ ≤ (9 * (1 + X) ^ 2) *
          (exp (4 * Real.pi * sqrt (a * X)) *
            exp (-(2 * Real.pi / sqrt U) * q)) :=
        mul_le_mul hp (referenceExp_sub_le_uniform (by linarith) hX hU hXU hq hqX)
          (exp_pos _).le (by positivity)
      _ = _ := by ring
  · rw [cellEnvelopeMass_eq_zero_of_nonpos (by linarith)]
    positivity

/-- One actual left-right descendant contribution to the finite-energy mass. -/
def cellEnvelopeDescendantMassTerm (a T X : ℝ) (p : ℕ × ℕ) : ℝ :=
  (partitionCount p.1 : ℝ) * (partitionCount p.2 : ℝ) *
    cellEnvelopeMass a T (X - ((p.1 : ℝ) + (p.2 : ℝ)))

theorem cellEnvelopeDescendantMassTerm_nonneg {a T X : ℝ} (ha : 100 ≤ a) (p : ℕ × ℕ) :
    0 ≤ cellEnvelopeDescendantMassTerm a T X p := by
  exact mul_nonneg (by positivity) (cellEnvelopeMass_nonneg ha)

theorem cellEnvelopeDescendantMassTerm_le {a T X U : ℝ}
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hX : 0 < X) (hU : 0 < U)
    (hXU : X ≤ U * a) (p : ℕ × ℕ) :
    cellEnvelopeDescendantMassTerm a T X p ≤
      (9 * (1 + X) ^ 2 * exp (4 * Real.pi * sqrt (a * X))) *
        (partitionThermalTerm (2 * Real.pi / sqrt U) p.1 *
          partitionThermalTerm (2 * Real.pi / sqrt U) p.2) := by
  dsimp only [cellEnvelopeDescendantMassTerm]
  have h := mul_le_mul_of_nonneg_left
    (cellEnvelopeMass_sub_le_boltzmann ha hT hX hU hXU
      (show 0 ≤ (p.1 : ℝ) + (p.2 : ℝ) by positivity))
    (show 0 ≤ (partitionCount p.1 : ℝ) * (partitionCount p.2 : ℝ) by positivity)
  convert h using 1
  dsimp only [partitionThermalTerm]
  rw [show -(2 * Real.pi / sqrt U) * ((p.1 : ℝ) + (p.2 : ℝ)) =
    -(2 * Real.pi / sqrt U) * (p.1 : ℝ) +
      -(2 * Real.pi / sqrt U) * (p.2 : ℝ) by ring, exp_add]
  ring

/-- Summability of the actual descendant-weighted reference mass. -/
theorem cellEnvelopeMass_descendant_summable {a T X U : ℝ}
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hX : 0 < X) (hU : 0 < U)
    (hXU : X ≤ U * a) : Summable (cellEnvelopeDescendantMassTerm a T X) := by
  have hs := summable_partitionThermalTerm
    (show 0 < 2 * Real.pi / sqrt U by positivity)
  have hprod := hs.mul_of_nonneg hs (partitionThermalTerm_nonneg _)
    (partitionThermalTerm_nonneg _)
  have hmajor := hprod.mul_left (9 * (1 + X) ^ 2 * exp (4 * Real.pi * sqrt (a * X)))
  exact hmajor.of_nonneg_of_le (cellEnvelopeDescendantMassTerm_nonneg ha)
    (cellEnvelopeDescendantMassTerm_le ha hT hX hU hXU)

/-- Every descendant and spin is included, at the unchanged BTZ exponential
rate and a charge-independent thermal factor. -/
theorem cellEnvelopeMass_descendant_le {a T X U : ℝ}
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hX : 0 < X) (hU : 0 < U)
    (hXU : X ≤ U * a) :
    (∑' p : ℕ × ℕ, (partitionCount p.1 : ℝ) * (partitionCount p.2 : ℝ) *
      cellEnvelopeMass a T (X - ((p.1 : ℝ) + (p.2 : ℝ)))) ≤
        9 * (1 + X) ^ 2 * exp (4 * Real.pi * sqrt (a * X)) *
          partitionThermal (2 * Real.pi / sqrt U) ^ 2 := by
  have hs := summable_partitionThermalTerm
    (show 0 < 2 * Real.pi / sqrt U by positivity)
  have hprod := hs.mul_of_nonneg hs (partitionThermalTerm_nonneg _)
    (partitionThermalTerm_nonneg _)
  have hmajor := hprod.mul_left (9 * (1 + X) ^ 2 * exp (4 * Real.pi * sqrt (a * X)))
  have h := (cellEnvelopeMass_descendant_summable ha hT hX hU hXU).tsum_le_tsum
    (cellEnvelopeDescendantMassTerm_le ha hT hX hU hXU) hmajor
  simpa only [cellEnvelopeDescendantMassTerm, tsum_mul_left,
    ← hs.tsum_mul_tsum hs hprod, ← pow_two, partitionThermal] using h

/-- An explicit constant can replace the convergent partition thermal factor. -/
theorem cellEnvelopeMass_descendant_le_exp {a T X U : ℝ}
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hX : 0 < X) (hU : 0 < U)
    (hXU : X ≤ U * a) :
    (∑' p : ℕ × ℕ, (partitionCount p.1 : ℝ) * (partitionCount p.2 : ℝ) *
      cellEnvelopeMass a T (X - ((p.1 : ℝ) + (p.2 : ℝ)))) ≤
        9 * (1 + X) ^ 2 * exp (4 * Real.pi * sqrt (a * X)) *
          exp (4 / (2 * Real.pi / sqrt U)) := by
  apply (cellEnvelopeMass_descendant_le ha hT hX hU hXU).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hb := partitionThermal_le_exp (show 0 < 2 * Real.pi / sqrt U by positivity)
  have hn : 0 ≤ partitionThermal (2 * Real.pi / sqrt U) :=
    tsum_nonneg (partitionThermalTerm_nonneg _)
  calc
    _ ≤ exp (2 / (2 * Real.pi / sqrt U)) ^ 2 := by gcongr
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

/-- Any genuinely finite descendant packet obeys the same bound as the
whole convergent tower; the constant does not depend on its cutoff. -/
theorem cellEnvelopeMass_descendant_finset_le {a T X U : ℝ}
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hX : 0 < X) (hU : 0 < U)
    (hXU : X ≤ U * a) (F : Finset (ℕ × ℕ)) :
    (∑ p ∈ F, (partitionCount p.1 : ℝ) * (partitionCount p.2 : ℝ) *
      cellEnvelopeMass a T (X - ((p.1 : ℝ) + (p.2 : ℝ)))) ≤
        9 * (1 + X) ^ 2 * exp (4 * Real.pi * sqrt (a * X)) *
          partitionThermal (2 * Real.pi / sqrt U) ^ 2 := by
  have hfin := Summable.sum_le_tsum F
    (fun p _ => cellEnvelopeDescendantMassTerm_nonneg ha p)
    (cellEnvelopeMass_descendant_summable ha hT hX hU hXU)
  exact hfin.trans (cellEnvelopeMass_descendant_le ha hT hX hU hXU)

/-- A fully explicit bound also holds for every finite packet. -/
theorem cellEnvelopeMass_descendant_finset_le_exp {a T X U : ℝ}
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hX : 0 < X) (hU : 0 < U)
    (hXU : X ≤ U * a) (F : Finset (ℕ × ℕ)) :
    (∑ p ∈ F, (partitionCount p.1 : ℝ) * (partitionCount p.2 : ℝ) *
      cellEnvelopeMass a T (X - ((p.1 : ℝ) + (p.2 : ℝ)))) ≤
        9 * (1 + X) ^ 2 * exp (4 * Real.pi * sqrt (a * X)) *
          exp (4 / (2 * Real.pi / sqrt U)) := by
  have hfin := Summable.sum_le_tsum F
    (fun p _ => cellEnvelopeDescendantMassTerm_nonneg ha p)
    (cellEnvelopeMass_descendant_summable ha hT hX hU hXU)
  exact hfin.trans (cellEnvelopeMass_descendant_le_exp ha hT hX hU hXU)

end BTZEntropy.Comparison
