import GapFamily.Construction.TailRepairBudget
import GapFamily.Construction.TailCellExistence

/-! The actual signed residual supplied by C8 has precisely the ordinary TV
budget required to apply C2 on the literal layer cutoff and moment schedule. -/

noncomputable section
open Set MeasureTheory Real
open GapFamily.Analytic
namespace GapFamily.Construction

/-- The actual cell's ordinary total variation has a uniform scheduled bound. -/
theorem TailCell.variation_le_schedule_exp {a m k : ℕ} {L : ℝ} {j : ℤ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (ha : (100 : ℝ) ≤ a) (hL : 1 ≤ L)
    (hLm : L < (m : ℝ) + 1) (hj : |(j : ℝ)| ≤ L)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt ((a : ℝ) * E))) :
    cell.residual.variation.real univ ≤ exp ((4 * π + 14) * ((a : ℝ) + m + 1)) := by
  have hlog := cell.log_variation_le ha hL hj herror
  have hscale : (4 * π + 14) * ((a : ℝ) + L) ≤
      (4 * π + 14) * ((a : ℝ) + m + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h := (log_le_iff_le_exp
    (by positivity : 0 < 2 + cell.residual.variation.real univ)).mp (hlog.trans hscale)
  linarith

/-- Once the actual C2 exterior estimate is supplied, an actual C8 cell pays
the complete slot allowance. Its TV and cutoff estimates are discharged here. -/
theorem TailCell.repair_error_le_slotBudget {a m U K p : ℕ} {L : ℝ}
    {j : ℤ} {q : ℝ → ℝ} (cell : TailCell j L (tailMomentDegree K a m) q)
    (ha : (100 : ℝ) ≤ a) (hL : 1 ≤ L) (hLm : L < (m : ℝ) + 1)
    (hj : |(j : ℝ)| ≤ L) (hU : U ≤ a)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt ((a : ℝ) * E)))
    {A C D e qout : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (he : ((U + m + 4 : ℕ) : ℝ) ≤ e)
    (hcharge : D + 2 * p ≤ 7 * sqrt a)
    (hK : tailRepairExponent A C (4 * π + 14) p + 16 ≤ (K : ℝ) * log 2)
    (hout : |qout| ≤ A * cell.residual.variation.real univ *
      (1 + ((U + m + 4 : ℕ) : ℝ) + e)^p *
      exp (C * ((U + m + 4 : ℕ) : ℝ) + D * sqrt e -
        (tailMomentDegree K a m : ℝ) * log 2)) :
    |qout| ≤ Layer.slotBudget m * exp (7 * sqrt ((a : ℝ) * e)) := by
  have hB : (1 : ℝ) ≤ ((U + m + 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ U + m + 4)
  exact tail_repair_error_le_slotBudget hA hC (Nat.cast_nonneg _)
    (tail_layer_cutoff_le_four_scale hU) (cell.variation_le_schedule_exp ha hL hLm hj herror)
    (hB.trans he) hcharge hK hout

end GapFamily.Construction
