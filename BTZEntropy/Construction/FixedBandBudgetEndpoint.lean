import BTZEntropy.Construction.FixedBandBudget
import BTZEntropy.Construction.FixedBandBudgetLimit

/-!
# Uniform initial exterior budget at a fixed endpoint

The charge threshold is chosen before the marker and the actual quadrature
cells. It controls every atom selector satisfying the initial-cell contract.
-/

noncomputable section

open Filter Real Set MeasureTheory
open GapFamily.Analytic GapFamily.Construction
open scoped Topology BigOperators

namespace BTZEntropy.Construction

theorem tendsto_fixedBandRepairCellBudget_zero {Q U B : ℝ}
    (hQ : 1 ≤ Q) (hU : 0 < U) (hB : 0 ≤ B) :
    Tendsto (fun a : ℝ => fixedBandRepairCellBudget Q a U fixedBandRepairRatio B
      (fixedBandDegree a U)) atTop (𝓝 0) := by
  have hA : 0 ≤ 2 * canonicalRepairCellCoefficient *
      fixedCutoffReferenceCompactMassCoefficient (Q + 1) := by
    have := canonicalRepairCellCoefficient_pos
    have := fixedCutoffReferenceCompactMassCoefficient_pos (Q + 1) (by linarith)
    positivity
  exact tendsto_fixedBand_budget_zero 10 hA hB
    (fixedCutoffReferenceCompactMassExponent_pos 2).le hU
    (by linarith [fixedBandRepairRatio_two_le]) fixedBandRepairRatio_log_gain

/-- A fixed finite collection of initial rows has a vanishing normalized
exterior budget on the full continuous charge axis. -/
theorem tendsto_fixedBandRepairRowBudget_zero (S : Finset ℤ) {Q U B : ℝ}
    (hQ : 1 ≤ Q) (hU : 0 < U) (hB : 0 ≤ B) :
    Tendsto (fun a : ℝ => (S.card : ℝ) *
      fixedBandRepairCellBudget Q a U fixedBandRepairRatio B (fixedBandDegree a U))
      atTop (𝓝 0) := by
  simpa only [mul_zero] using
    (tendsto_fixedBandRepairCellBudget_zero hQ hU hB).const_mul (S.card : ℝ)

/-- The same threshold enforces the analytic Cauchy geometry and any
prescribed positive budget, uniformly in the eventual marker and cells. -/
theorem exists_fixedBandRepair_threshold (S : Finset ℤ) {b Q U ε : ℝ}
    (hQ : 1 ≤ Q) (hU : 1 ≤ U) (hε : 0 < ε) :
    ∃ A : ℝ, 2 ≤ A ∧ b ≤ A ∧ ∀ a : ℝ, A ≤ a →
      10000 * fixedBandRepairRatio ^ 2 * (U + 1) ≤ a ∧
      (S.card : ℝ) * fixedBandRepairCellBudget Q a U fixedBandRepairRatio
        (2 * U + 4) (fixedBandDegree a U) ≤ ε := by
  have hlim := tendsto_fixedBandRepairRowBudget_zero S hQ
    (by linarith : 0 < U) (by linarith : 0 ≤ 2 * U + 4)
  have hbudget := (hlim.eventually (gt_mem_nhds hε)).mono fun _ h => h.le
  have hall : ∀ᶠ a : ℝ in atTop, 2 ≤ a ∧ b ≤ a ∧
      10000 * fixedBandRepairRatio ^ 2 * (U + 1) ≤ a ∧
      (S.card : ℝ) * fixedBandRepairCellBudget Q a U fixedBandRepairRatio
        (2 * U + 4) (fixedBandDegree a U) ≤ ε := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop b,
      eventually_ge_atTop (10000 * fixedBandRepairRatio ^ 2 * (U + 1)), hbudget]
      with a ha hb hwidth hsmall
    exact ⟨ha, hb, hwidth, hsmall⟩
  obtain ⟨A, hA⟩ := eventually_atTop.mp hall
  exact ⟨A, (hA A le_rfl).1, (hA A le_rfl).2.1,
    fun a ha => (hA a ha).2.2⟩

/-- Every marker in the cleared interval and every admissible initial atom
selection satisfy the normalized exterior estimate above one common charge
threshold. This includes the threshold marker `δ = 0`. -/
theorem exists_fixedBand_initialRepair_bound (S : Finset ℤ) {b Q U ε : ℝ}
    (hb : 1 ≤ b) (hQ : 1 ≤ Q) (hU : 1 ≤ U) (hQU : U = Q * b)
    (hε : 0 < ε) :
    ∃ A : ℝ, 2 ≤ A ∧ b ≤ A ∧ ∀ a : ℝ, A ≤ a →
      ∀ (ha : 2 ≤ a) (δ : ℝ), 0 ≤ δ → δ ≤ b →
      ∀ cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) U
        (fixedBandDegree a U) (fixedCutoffReferenceDensity a b δ ha hb J),
      ∀ (j : ℤ) (e : ℝ), |(j : ℝ)| ≤ e →
      (∑ J, |if 2 * U + 4 < e then
        (cells J).exteriorNumerator (2 * U + 4) (by linarith) j e else 0|) ≤
        ε * exp (7 * sqrt (a * e)) := by
  obtain ⟨A, hA2, hAb, hA⟩ := exists_fixedBandRepair_threshold S hQ hU hε
  refine ⟨A, hA2, hAb, ?_⟩
  intro a haa ha δ hδ hδb cells j e he
  obtain ⟨hcharge, hbudget⟩ := hA a haa
  exact (fixedBand_sum_abs_exteriorIndicator_le cells hδ hδb hU
    fixedBandRepairRatio_two_le hQ (hAb.trans haa) hQU hcharge j e he).trans
      (mul_le_mul_of_nonneg_right hbudget (exp_nonneg _))

end BTZEntropy.Construction
