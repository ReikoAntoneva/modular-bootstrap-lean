import GapFamily.Construction.CanonicalInitialRepairBudget
import GapFamily.Construction.InitialReferenceCellMass
import GapFamily.Construction.InitialReferenceCellRepairDensity

/-!
# Exterior budget for one actual initial reference-cell repair

The literal cell residual supplies the vanishing coordinate moments in the
canonical repair estimate. Its proved signed variation bound gives an
explicit degree-decaying exterior budget, for both complex and real output.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The full normalized exterior budget for one canonical initial cell. -/
def initialReferenceRepairCellBudget (R s n : ℕ) (B : ℝ) : ℝ :=
  2 * canonicalRepairCellCoefficient * markerReferenceCompactMassCoefficient ((R : ℝ) + 1) *
    (1 + ((R * s ^ 2 * n : ℕ) : ℝ) + B) ^ 10 *
    exp (markerReferenceCompactMassExponent ((R : ℝ) + 1) * ((R * s * n : ℕ) : ℝ) +
      canonicalRepairKernelExponent * B) / (initialRepairRatio s) ^ (R * s * n)

theorem initialReferenceRepairCellBudget_nonneg (R s n : ℕ) {B : ℝ}
    (hB : 1 ≤ B) (hρ : 2 ≤ initialRepairRatio s) :
    0 ≤ initialReferenceRepairCellBudget R s n B := by
  unfold initialReferenceRepairCellBudget
  have := canonicalRepairCellCoefficient_pos
  have := markerReferenceCompactMassCoefficient_pos ((R : ℝ) + 1) (by positivity)
  have hρ0 : 0 < initialRepairRatio s := by linarith
  positivity

namespace InitialReferenceCell

/-- The cell's actual square-root pushforward has all required vanishing
moments, with the endpoint support supplied by the cell itself. -/
theorem signedSqrtCoordinate_moment_zero {jin : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell jin L U k q) (m : ℕ) (hm : m ≤ k) :
    (∫ᵛ x : ℝ, x ^ m ∂<•signedSqrtCoordinate jin cell.residual) = 0 := by
  rw [signedSqrtCoordinate_moment jin cell.residual cell.ae_mem_cell m]
  simpa only [InitialReferenceCell.residual, Polynomial.eval_pow, Polynomial.eval_X, rootCoord]
    using (cell.moment (Polynomial.X ^ m) (by simpa using hm)).2

variable {R s n : ℕ} {jin : ℤ}
  {ha : 2 ≤ ((R * s ^ 2 * n : ℕ) : ℝ)} {hb : 1 ≤ (n : ℝ)}
  (cell : InitialReferenceCell jin (max (n : ℝ) |(jin : ℝ)|) ((R * n : ℕ) : ℝ)
    (R * s * n) (canonicalMarkerReferenceDensity ((R * s ^ 2 * n : ℕ) : ℝ)
      (n : ℝ) ha hb jin))

/-- The complex canonical exterior response of this literal initial cell
satisfies the normalized degree-decaying budget. -/
theorem norm_canonicalExterior_le_initial_budget
    (hR : 1 ≤ R) (hs : 1 ≤ s) (hn : 1 ≤ n) (hρ : 2 ≤ initialRepairRatio s)
    (B : ℝ) (hB : 1 ≤ B) (hcut : cell.right < B)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    ‖canonicalRepairExteriorNumerator (singleSpinInput jin cell.residual) B hB j e‖ ≤
      initialReferenceRepairCellBudget R s n B *
        exp (7 * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * e)) := by
  have hbase := norm_canonicalInitialRepairExterior_le hR hs hn hρ B hB j jin e he hBe
    cell.residual (max (n : ℝ) |(jin : ℝ)|) cell.right (le_max_right _ _)
    cell.left_le_right hcut cell.right_mem.2 cell.ae_mem_cell
    (fun m hm => cell.signedSqrtCoordinate_moment_zero m hm)
  rw [SignedMeasure.totalVariation_eq_variation] at hbase
  have htv := cell.variation_le_canonical_parameter R s n hR hs ha hb jin
  have hpoly : (1 + ((R * s ^ 2 * n : ℕ) : ℝ)) ^ 9 ≤
      (1 + ((R * s ^ 2 * n : ℕ) : ℝ) + B) ^ 9 := by
    apply pow_le_pow_left₀ (by positivity) (by linarith) 9
  have hC := canonicalRepairCellCoefficient_pos.le
  have hM := (markerReferenceCompactMassCoefficient_pos ((R : ℝ) + 1) (by positivity)).le
  have hρ0 : 0 < initialRepairRatio s := by linarith
  have htv' : cell.residual.variation.real univ ≤
      2 * markerReferenceCompactMassCoefficient ((R : ℝ) + 1) *
        (1 + ((R * s ^ 2 * n : ℕ) : ℝ) + B) ^ 9 *
        exp (markerReferenceCompactMassExponent ((R : ℝ) + 1) * ((R * s * n : ℕ) : ℝ)) := by
    exact htv.trans (by gcongr)
  refine hbase.trans ?_
  calc
    _ ≤ canonicalRepairCellCoefficient *
        (2 * markerReferenceCompactMassCoefficient ((R : ℝ) + 1) *
          (1 + ((R * s ^ 2 * n : ℕ) : ℝ) + B) ^ 9 *
          exp (markerReferenceCompactMassExponent ((R : ℝ) + 1) * ((R * s * n : ℕ) : ℝ))) *
        (1 + ((R * s ^ 2 * n : ℕ) : ℝ) + B) * exp (canonicalRepairKernelExponent * B) /
          (initialRepairRatio s) ^ (R * s * n) *
            exp (7 * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * e)) := by gcongr
    _ = _ := by unfold initialReferenceRepairCellBudget; rw [exp_add]; ring

/-- The real ordinary exterior numerator inherits the same proved budget. -/
theorem abs_exteriorNumerator_le_initial_budget
    (hR : 1 ≤ R) (hs : 1 ≤ s) (hn : 1 ≤ n) (hρ : 2 ≤ initialRepairRatio s)
    (B : ℝ) (hB : 1 ≤ B) (hcut : cell.right < B)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    |cell.exteriorNumerator B hB j e| ≤
      initialReferenceRepairCellBudget R s n B *
        exp (7 * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * e)) := by
  exact (Complex.abs_re_le_norm _).trans
    (cell.norm_canonicalExterior_le_initial_budget hR hs hn hρ B hB hcut j e he hBe)

/-- The prescribed repair band lies strictly beyond the entire initial cell. -/
theorem right_lt_initial_repairBand : cell.right < 2 * ((R * n : ℕ) : ℝ) + 4 := by
  have hn0 : (0 : ℝ) ≤ ((R * n : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith [cell.right_mem.2]

/-- Specialization to the actual frozen repair band `B₀ = 2 U + 4`. -/
theorem abs_exteriorNumerator_initial_repairBand_le
    (hR : 1 ≤ R) (hs : 1 ≤ s) (hn : 1 ≤ n) (hρ : 2 ≤ initialRepairRatio s)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e)
    (hBe : 2 * ((R * n : ℕ) : ℝ) + 4 ≤ e) :
    |cell.exteriorNumerator (2 * ((R * n : ℕ) : ℝ) + 4)
        (by have := Nat.cast_nonneg (α := ℝ) (R * n); linarith) j e| ≤
      initialReferenceRepairCellBudget R s n (2 * ((R * n : ℕ) : ℝ) + 4) *
        exp (7 * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * e)) :=
  cell.abs_exteriorNumerator_le_initial_budget hR hs hn hρ _
    (by have := Nat.cast_nonneg (α := ℝ) (R * n); linarith)
    cell.right_lt_initial_repairBand j e he hBe

end InitialReferenceCell
end GapFamily.Construction
