import GapFamily.Construction.FixedCutoffInitialRepair
import GapFamily.Construction.ProportionalRepairBudget

/-!
# Ordered budget for the actual fixed-cutoff initial repair

The auxiliary ratio is fixed before the processing-to-clearing cutoff ratio. Its
uniform logarithmic gain absorbs the actual finite initial repair sum on
every sufficiently large real charge.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

theorem fixedCutoffInitialRepairBudget_nonneg {Q a B : ℝ} {s : ℕ}
    (hQ : 1 ≤ Q) (ha : 0 ≤ a) (hB : 0 ≤ B) (hρ : 2 ≤ initialRepairRatio s) :
    0 ≤ fixedCutoffInitialRepairBudget Q a s B := by
  have := canonicalRepairCellCoefficient_pos
  have := fixedCutoffReferenceCompactMassCoefficient_pos (Q + 1) (by linarith)
  have hρ0 : 0 < initialRepairRatio s := by linarith
  unfold fixedCutoffInitialRepairBudget
  positivity

/-- The exterior indicator preserves the actual total estimate on all
physical output energies, including below the common repair band. -/
theorem sum_abs_fixedCutoffInitialRepairExterior_indicator_le_budget
    {S : Finset ℤ} {a b δ Q : ℝ} {s : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) (proportionalCutoff a s)
      (proportionalDegree a s) (fixedCutoffReferenceDensity a b δ ha hb J))
    (hδ : 0 ≤ δ) (hδb : δ ≤ b)
    (hs : 1 ≤ s) (hρ : 2 ≤ initialRepairRatio s)
    (hU : 1 ≤ proportionalCutoff a s) (hlarge : 2 ≤ a / s)
    (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : proportionalCutoff a s = Q * b)
    (hcard : (S.card : ℝ) ≤ 10 * (1 + a))
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    (∑ J, |if 2 * proportionalCutoff a s + 4 < e then
      (cells J).exteriorNumerator (2 * proportionalCutoff a s + 4)
        (by linarith) j e else 0|) ≤
      fixedCutoffInitialRepairBudget Q a s (2 * proportionalCutoff a s + 4) *
        exp (7 * sqrt (a * e)) := by
  by_cases hBe : 2 * proportionalCutoff a s + 4 < e
  · simp_rw [ite_eq_left hBe]
    exact sum_abs_fixedCutoffInitialRepairExterior_le_budget cells hδ hδb hs hρ hU hlarge
      hQ hba hQU hcard _ (by linarith)
      (fun J => by linarith [(cells J).right_mem.2]) j e he hBe.le
  · simp only [ite_eq_right hBe, abs_zero, Finset.sum_const_zero]
    exact mul_nonneg (fixedCutoffInitialRepairBudget_nonneg hQ (by linarith)
      (by linarith) hρ) (exp_nonneg _)

/-- One fixed auxiliary ratio absorbs the actual initial repair budget for
every later fixed real band ratio. The real charge threshold can depend
on that band ratio. -/
theorem exists_fixedCutoffInitialRepair_budget_ratio :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s →
      2 ≤ initialRepairRatio s ∧ ∀ Q : ℝ, 1 ≤ Q →
      ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a →
        fixedCutoffInitialRepairBudget Q a s
          (2 * proportionalCutoff a s + 4) ≤ 1 / 8 := by
  obtain ⟨s₀, hs₀, hs⟩ := exists_proportionalRepair_budget_ratio
    (Ck := 2 * fixedCutoffReferenceCompactMassExponent 2) (CU := 0)
    (CB := canonicalRepairKernelExponent)
    (by have := fixedCutoffReferenceCompactMassExponent_pos 2; positivity)
    (by norm_num) canonicalRepairKernelExponent_pos.le
  refine ⟨s₀, hs₀, ?_⟩
  intro s hss
  obtain ⟨hρ, _, hbudget⟩ := hs s hss
  refine ⟨hρ, ?_⟩
  intro Q hQ
  have hcoeff : 0 ≤ 20 * canonicalRepairCellCoefficient *
      fixedCutoffReferenceCompactMassCoefficient (Q + 1) := by
    have := canonicalRepairCellCoefficient_pos
    have := fixedCutoffReferenceCompactMassCoefficient_pos (Q + 1) (by linarith)
    positivity
  obtain ⟨a₀, ha₀, ha⟩ := hbudget _ hcoeff 11
  refine ⟨a₀, ha₀, ?_⟩
  intro a haa
  simpa only [fixedCutoffInitialRepairBudget, zero_mul, add_zero] using ha a haa

end GapFamily.Construction
