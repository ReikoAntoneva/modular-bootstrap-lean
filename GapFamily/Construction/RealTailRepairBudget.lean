import GapFamily.Construction.RealTailCell
import GapFamily.Construction.CanonicalTailRepairBudget

/-! Repair budgets for a real vacuum parameter and a real initial cutoff.
Only the number of cancelled moments is rounded; the vacuum density and the
cutoff in the canonical repair retain their original real values. -/

noncomputable section

open Set MeasureTheory Real Filter
open GapFamily.Analytic

namespace GapFamily.Construction

/-- An actual tail cell has the scheduled variation bound at a real charge. -/
theorem TailCell.variation_le_real_schedule_exp {a L : ℝ} {m k : ℕ}
    {j : ℤ} {q : ℝ → ℝ} (cell : TailCell j L k q)
    (ha : 100 ≤ a) (hL : 1 ≤ L) (hLm : L < (m : ℝ) + 1)
    (hj : |(j : ℝ)| ≤ L)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    cell.residual.variation.real univ ≤ exp ((4 * π + 14) * (a + m + 1)) := by
  have hlog := cell.log_variation_le ha hL hj herror
  have hscale : (4 * π + 14) * (a + L) ≤
      (4 * π + 14) * (a + m + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h := (log_le_iff_le_exp
    (by positivity : 0 < 2 + cell.residual.variation.real univ)).mp (hlog.trans hscale)
  linarith

/-- The real layer cutoff is controlled by the real charge and layer scale. -/
theorem real_tail_layer_cutoff_le_four_scale {U a : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hU : U ≤ a) :
    U + m + 4 ≤ 4 * (a + m + 1) := by
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- The exterior estimate pays its literal slot allowance at the real charge;
rounding is confined to the integer moment schedule. -/
theorem real_tail_repair_error_le_slotBudget {A C D V B tv q e a : ℝ} {m K p : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hBupper : B ≤ 4 * (a + m + 1))
    (htvbound : tv ≤ exp (V * (a + m + 1))) (he : 1 ≤ e)
    (hcharge : D + 2 * p ≤ 7 * sqrt a)
    (hK : tailRepairExponent A C V p + 16 ≤ (K : ℝ) * log 2)
    (hq : |q| ≤ A * tv * (1 + B + e)^p *
      exp (C * B + D * sqrt e - (realTailMomentDegree K a m : ℝ) * log 2)) :
    |q| ≤ Layer.slotBudget m * exp (7 * sqrt (a * e)) := by
  let X : ℝ := a + m + 1
  let d : ℝ := (realTailMomentDegree K a m : ℝ) * log 2
  have hX : 1 ≤ X := by
    dsimp [X]
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hpoly := tail_exterior_polynomial_absorption (A := A) (C := C)
    (D := D) (a := a) p hB he ha hcharge
  have hcost : V * X + (|A| + (C + p) * B + 2 * p) ≤
      tailRepairExponent A C V p * X := by
    have h1 := mul_le_mul_of_nonneg_left hBupper
      (by positivity : 0 ≤ C + (p : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hX
      (by positivity : 0 ≤ |A| + 2 * (p : ℝ))
    dsimp [tailRepairExponent]
    change B ≤ 4 * X at hBupper
    change (C + (p : ℝ)) * B ≤ (C + (p : ℝ)) * (4 * X) at h1
    nlinarith
  calc
    |q| ≤ A * tv * (1 + B + e)^p * exp (C * B + D * sqrt e - d) := hq
    _ = tv * (A * (1 + B + e)^p * exp (C * B + D * sqrt e)) *
        exp (-d) := by rw [sub_eq_add_neg, exp_add]; ring
    _ ≤ exp (V * X) *
        (exp (|A| + (C + p) * B + 2 * p) * exp (7 * sqrt (a * e))) * exp (-d) := by
      apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
      exact mul_le_mul htvbound hpoly (by positivity) (exp_nonneg _)
    _ = exp (V * X + (|A| + (C + p) * B + 2 * p) - d) *
        exp (7 * sqrt (a * e)) := by
      simp only [sub_eq_add_neg, exp_add]
      ring
    _ ≤ exp (tailRepairExponent A C V p * X - d) * exp (7 * sqrt (a * e)) :=
      mul_le_mul_of_nonneg_right (exp_le_exp.mpr (sub_le_sub_right hcost d)) (exp_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (realTailMomentDegree_error_le_slotBudget hK a ha m) (exp_nonneg _)

/-- The actual real-charge tail cell supplies the variation and real cutoff
bounds required by the abstract exterior repair estimate. -/
theorem TailCell.real_repair_error_le_slotBudget {a U L : ℝ} {m K p : ℕ}
    {j : ℤ} {q : ℝ → ℝ} (cell : TailCell j L (realTailMomentDegree K a m) q)
    (ha : 100 ≤ a) (hL : 1 ≤ L) (hLm : L < (m : ℝ) + 1)
    (hj : |(j : ℝ)| ≤ L) (hU₀ : 0 ≤ U) (hU : U ≤ a)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E)))
    {A C D e qout : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (he : U + m + 4 ≤ e)
    (hcharge : D + 2 * p ≤ 7 * sqrt a)
    (hK : tailRepairExponent A C (4 * π + 14) p + 16 ≤ (K : ℝ) * log 2)
    (hout : |qout| ≤ A * cell.residual.variation.real univ * (1 + (U + m + 4) + e)^p *
      exp (C * (U + m + 4) + D * sqrt e -
        (realTailMomentDegree K a m : ℝ) * log 2)) :
    |qout| ≤ Layer.slotBudget m * exp (7 * sqrt (a * e)) := by
  have hB : (1 : ℝ) ≤ U + m + 4 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  exact real_tail_repair_error_le_slotBudget hA hC (by linarith)
    (by positivity) (real_tail_layer_cutoff_le_four_scale (by linarith) hU)
    (cell.variation_le_real_schedule_exp ha hL hLm hj herror)
    (hB.trans he) hcharge hK hout

/-- The complete canonical exterior repair of a real-charge cell pays its
slot allowance at the real layer cutoff, for every physical output spin. -/
theorem TailCell.real_exteriorNumerator_le_slotBudget {a U L : ℝ} {m K : ℕ}
    {J : ℤ} {q : ℝ → ℝ} (cell : TailCell J L (realTailMomentDegree K a m) q)
    (ha : 100 ≤ a) (hL : 1 ≤ L) (hLm : L < (m : ℝ) + 1)
    (hJ : |(J : ℝ)| ≤ L) (hU₀ : 0 ≤ U) (hU : U ≤ a)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E J| ≤ exp (7 * sqrt (a * E)))
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : U + m + 4 ≤ e)
    (hcharge : 4 * π + 4 ≤ 7 * sqrt a)
    (hK : tailRepairExponent canonicalRepairCellCoefficient canonicalRepairKernelExponent
      (4 * π + 14) 2 + 16 ≤ (K : ℝ) * log 2) :
    |cell.exteriorNumerator (U + m + 4)
      (by linarith [Nat.cast_nonneg (α := ℝ) m]) j e| ≤
      Layer.slotBudget m * exp (7 * sqrt (a * e)) := by
  have hB : (1 : ℝ) ≤ U + m + 4 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hcut : cell.right < U + m + 4 := by
    linarith [cell.right_mem.2]
  apply cell.real_repair_error_le_slotBudget (A := canonicalRepairCellCoefficient)
    (C := canonicalRepairKernelExponent) (D := 4 * π) (p := 2)
    ha hL hLm hJ hU₀ hU herror canonicalRepairCellCoefficient_pos.le
    canonicalRepairKernelExponent_pos.le hBe (by norm_num; exact hcharge) hK
  exact cell.exteriorNumerator_shortCell _ hB hJ hcut j e he hBe

/-- One threshold supplies the actual cell and all its canonical exterior
budgets, uniformly over every real cutoff below the charge. -/
theorem eventually_realTailCell_with_budget {t : ℝ} (ht : 0 < t) {K : ℕ}
    (hK : 0 < K)
    (hbudget : tailRepairExponent canonicalRepairCellCoefficient canonicalRepairKernelExponent
      (4 * π + 14) 2 + 16 ≤ (K : ℝ) * log 2) :
    ∀ᶠ a : ℝ in atTop, ∀ U : ℝ, ∀ hU₀ : 0 ≤ U, U ≤ a →
      ∀ m : ℕ, ∀ L : ℝ, t * a ≤ L → (m : ℝ) ≤ L → L < (m : ℝ) + 1 →
      ∀ J : ℤ, |(J : ℝ)| ≤ L →
      ∀ q : ℝ → ℝ, IntegrableOn q (Ioo L (L + 1)) (referenceMeasure J) →
      (∀ E ∈ Icc L (L + 1),
        |q E - vacuumLeading a E J| ≤ exp (7 * sqrt (a * E))) →
      ∃ cell : TailCell J L (realTailMomentDegree K a m) q,
        cell.residual.variation.real univ ≤ 12 * exp (4 * π * (a + L)) ∧
        ∀ j : ℤ, ∀ e : ℝ, |(j : ℝ)| ≤ e → U + m + 4 ≤ e →
          |cell.exteriorNumerator (U + m + 4)
            (by linarith [Nat.cast_nonneg (α := ℝ) m]) j e| ≤
            Layer.slotBudget m * exp (7 * sqrt (a * e)) := by
  filter_upwards [eventually_realTailCell ht hK, eventually_ge_atTop (100 : ℝ),
    eventually_ge_atTop (1 / t)] with a hcell ha hat
  intro U hU₀ hUa m L hray hmL hLm J hJ q hq herror
  obtain ⟨_, cell, hvar, _⟩ := hcell m L hray hmL hLm J hJ q hq herror
  have hL : 1 ≤ L := by
    have h := (div_le_iff₀ ht).mp hat
    nlinarith
  have hcharge : 4 * π + 4 ≤ 7 * sqrt a := by
    have hs : 10 ≤ sqrt a := Real.le_sqrt_of_sq_le (by nlinarith)
    nlinarith [Real.pi_lt_four]
  refine ⟨cell, hvar, ?_⟩
  intro j e hj hBe
  exact cell.real_exteriorNumerator_le_slotBudget ha hL hLm hJ hU₀ hUa herror
    j e hj hBe hcharge hbudget

end GapFamily.Construction
