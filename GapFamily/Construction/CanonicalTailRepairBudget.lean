import GapFamily.Construction.TailCellRepairBudget
import GapFamily.Construction.TailCellRepairDensity
import GapFamily.Analytic.Poincare.Repair.PoincareSingleSpinRepair
import GapFamily.Analytic.Poincare.Repair.PoincareTailExteriorEstimate

/-! The actual canonical repair of an actual tail cell pays its scheduled
exterior allowance. Moment cancellation, total variation, and the exterior
kernel estimate are proved for the literal residual, with no assumed repair
error bound.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The actual polynomial moments of a tail cell are exactly the ordinary
moments of its genuine square-root pushforward measure. -/
theorem TailCell.sqrtCoordinate_moment {J : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell J L k q) (n : ℕ) (hn : n ≤ k) :
    (∫ᵛ x : ℝ, x ^ n ∂<•signedSqrtCoordinate J cell.residual) = 0 := by
  rw [signedSqrtCoordinate_moment J cell.residual cell.residual_ae_mem n]
  have h := (cell.moment ((Polynomial.X : Polynomial ℝ) ^ n) (by simpa using hn)).2
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, rootCoord, TailCell.residual] using h

/-- The complete exterior numerator of the actual cell repair satisfies the
uniform short-cell C2 estimate, for every physical output spin. -/
theorem TailCell.exteriorNumerator_shortCell {J : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell J L k q) (B : ℝ) (hB : 1 ≤ B)
    (hJ : |(J : ℝ)| ≤ L) (hcut : cell.right < B)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    |cell.exteriorNumerator B hB j e| ≤
      canonicalRepairCellCoefficient * cell.residual.variation.real univ * (1 + B + e) ^ 2 *
        exp (canonicalRepairKernelExponent * B + 4 * π * sqrt e - (k : ℝ) * log 2) := by
  have hLV : L ≤ cell.right := by linarith [cell.right_mem.1]
  have hsingle : cell.rowInput = singleSpinInput J cell.residual := rfl
  unfold TailCell.exteriorNumerator
  rw [hsingle, canonicalRepairExteriorNumerator_singleSpin J cell.residual B hB
    (cell.input_spin_mem B hJ hcut)]
  apply (Complex.abs_re_le_norm _).trans
  simpa only [SignedMeasure.totalVariation_eq_variation] using
    norm_signedIntegral_canonicalRepairKernelEnergy_shortCell B hB j J e he hBe
      cell.residual L cell.right k hJ hLV hcut.le (by linarith [cell.right_mem.2])
      cell.residual_ae_mem cell.sqrtCoordinate_moment

/-- The actual modular repair of the actual moment-matched cell pays its
literal rational slot budget. All analytic C2 premises have been discharged. -/
theorem TailCell.exteriorNumerator_le_slotBudget {a m U K : ℕ} {L : ℝ}
    {J : ℤ} {q : ℝ → ℝ} (cell : TailCell J L (tailMomentDegree K a m) q)
    (ha : (100 : ℝ) ≤ a) (hL : 1 ≤ L) (hLm : L < (m : ℝ) + 1)
    (hJ : |(J : ℝ)| ≤ L) (hU : U ≤ a)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E J| ≤ exp (7 * sqrt ((a : ℝ) * E)))
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e)
    (hBe : ((U + m + 4 : ℕ) : ℝ) ≤ e)
    (hcharge : 4 * π + 4 ≤ 7 * sqrt a)
    (hK : tailRepairExponent canonicalRepairCellCoefficient canonicalRepairKernelExponent
      (4 * π + 14) 2 + 16 ≤ (K : ℝ) * log 2) :
    |cell.exteriorNumerator ((U + m + 4 : ℕ) : ℝ)
      (by exact_mod_cast (show 1 ≤ U + m + 4 by omega)) j e| ≤
        Layer.slotBudget m * exp (7 * sqrt ((a : ℝ) * e)) := by
  have hB : (1 : ℝ) ≤ ((U + m + 4 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ U + m + 4 by omega)
  have hcut : cell.right < ((U + m + 4 : ℕ) : ℝ) := by
    push_cast
    linarith [cell.right_mem.2, Nat.cast_nonneg (α := ℝ) U]
  apply cell.repair_error_le_slotBudget (A := canonicalRepairCellCoefficient)
    (C := canonicalRepairKernelExponent) (D := 4 * π) (p := 2) ha hL hLm hJ hU herror
    canonicalRepairCellCoefficient_pos.le canonicalRepairKernelExponent_pos.le hBe
    (by norm_num; exact hcharge) hK
  exact cell.exteriorNumerator_shortCell _ hB hJ hcut j e he hBe

end GapFamily.Construction
