import GapFamily.Construction.FixedCutoffInitialCell
import GapFamily.Construction.FixedCutoffInitialBudget
import GapFamily.Construction.RealInitialRow

/-!
# Actual fixed-marker initial data with ordered auxiliary constants

This closes the complete initial-cell existence and exterior error budget
for every sufficiently large real vacuum shift. The same auxiliary
integers and positive interval of gap ratios are used throughout.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

/-- The actual fixed-marker initial family, including every integer spin in
the closed reference window. -/
abbrev FixedCutoffInitialCellFamily (s : ℕ) (a κ δ : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ κ * a) :=
  ∀ J : realInitialRows ((fixedCutoffReferenceRadius : ℝ) * (κ * a)),
    InitialReferenceCell J (max (κ * a) |(J : ℝ)|)
      (proportionalCutoff a s)
      (proportionalDegree a s)
      (fixedCutoffReferenceDensity a
        (κ * a) δ ha hb J)

/-- Fixed auxiliary constants precede every real cutoff ratio `κ` in a positive
interval. Every sufficiently large real charge has actual initial
unit-node cells and total exterior error at most one eighth of the envelope.
No analytic cell or numerical budget premise remains. -/
theorem exists_fixedCutoff_initial_data :
    ∃ (R s : ℕ), 16 * fixedCutoffReferenceRadius ≤ R ∧ 11 ≤ s ∧
      2 ≤ initialRepairRatio s ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ κ : ℝ, 0 < κ → κ < κ₀ → ∀ δ : ℝ, 0 ≤ δ →
      ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a →
      ∃ (ha : 2 ≤ a) (hb : 1 ≤ κ * a),
      ∃ (hU : 1 ≤ proportionalCutoff a s),
      δ ≤ κ * a ∧
      (fixedCutoffReferenceBandThreshold : ℝ) ≤ κ * a ∧
      κ * a ≤ a ∧
      (fixedCutoffReferenceRadius : ℝ) * (κ * a) ≤
        proportionalCutoff a s ∧
      proportionalCutoff a s ≤ a ∧
      ∃ cells : FixedCutoffInitialCellFamily s a κ δ ha hb,
      ∀ (j : ℤ) (e : ℝ), |(j : ℝ)| ≤ e →
        (∑ J, |if 2 * proportionalCutoff a s + 4 < e then
          (cells J).exteriorNumerator
            (2 * proportionalCutoff a s + 4)
            (by linarith) j e else 0|) ≤
          exp (7 * sqrt (a * e)) / 8 := by
  obtain ⟨R, hR1, hR, hC⟩ := exists_initialParameter_radius fixedCutoffReferenceRadius
    fixedCutoffReferenceNegativeExponent fixedCutoffReferenceNegativeExponent_pos.le
  obtain ⟨s₀, hs₀, hs⟩ := exists_fixedCutoffInitialRepair_budget_ratio
  let s : ℕ := max 11 s₀
  have hs11 : 11 ≤ s := le_max_left _ _
  have hs1 : 1 ≤ s := by omega
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hs1r : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hR1r : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hRpos : (0 : ℝ) < R := by linarith
  obtain ⟨hρ, hbudget⟩ := hs s (le_max_right _ _)
  refine ⟨R, s, hR, hs11, hρ, 1 / (4 * R * (s : ℝ) ^ 2), by positivity, ?_⟩
  intro κ hκpos hκ δ hδ
  let Q : ℝ := 1 / (κ * (s : ℝ) ^ 2)
  have hκscale : κ * (s : ℝ) ^ 2 ≤ 1 := by
    have hm := (lt_div_iff₀ (show 0 < 4 * (R : ℝ) * (s : ℝ) ^ 2 by positivity)).mp hκ
    nlinarith [mul_nonneg (show 0 ≤ (R : ℝ) - 1 by linarith)
      (show 0 ≤ κ * (s : ℝ) ^ 2 by positivity)]
  have hκone : κ ≤ 1 := by
    nlinarith [mul_nonneg hκpos.le (show 0 ≤ (s : ℝ) ^ 2 - 1 by nlinarith)]
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa using hκscale)
  obtain ⟨Ai, hAi, hi⟩ := exists_fixedCutoff_initial_reference_cell hR hC hs1 hκpos hκ.le hδ
  obtain ⟨Ab, _, hb⟩ := hbudget Q hQ
  obtain ⟨Ad, _, hd⟩ := exists_proportionalParameter_degree_threshold hs1 0
  obtain ⟨Au, _, hu⟩ := exists_proportionalParameter_charge_threshold ((s : ℝ) ^ 2)
  obtain ⟨Ar, _, hr⟩ := exists_proportionalParameter_gap_threshold hκpos
    (fixedCutoffReferenceBandThreshold : ℝ)
  refine ⟨max Ai (max Ab (max Ad (max Au Ar))), hAi.trans (le_max_left _ _), ?_⟩
  intro a haa
  have hAia : Ai ≤ a := (le_max_left _ _).trans haa
  have hAba : Ab ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans haa)
  have hAda : Ad ≤ a := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans haa))
  have hAua : Au ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans haa)))
  have hAra : Ar ≤ a := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans haa)))
  obtain ⟨ha, hb', hδb, hcells⟩ := hi a hAia
  have ha0 : 0 ≤ a := by linarith
  have hU : 1 ≤ proportionalCutoff a s := by
    unfold proportionalCutoff
    exact (le_div_iff₀ (by positivity)).mpr (by simpa using hu a hAua)
  have hlarge := (hd a hAda).2
  have hba : κ * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right hκone ha0
  have hQU : proportionalCutoff a s = Q * (κ * a) := by
    dsimp [proportionalCutoff, Q]
    field_simp
  have hT0 : 0 ≤ (fixedCutoffReferenceRadius : ℝ) * (κ * a) := by positivity
  have hTU : (fixedCutoffReferenceRadius : ℝ) * (κ * a) ≤
      proportionalCutoff a s := by
    have hgap := proportionalParameter_gap_le_cutoff ha0 hR1 hs1 hκ.le
    have hm := (le_div_iff₀ (show 0 < 4 * (R : ℝ) by positivity)).mp hgap
    have hRr : (fixedCutoffReferenceRadius : ℝ) ≤ R := by
      exact_mod_cast (show fixedCutoffReferenceRadius ≤ R by omega)
    have hscale := mul_le_mul_of_nonneg_right hRr
      (show 0 ≤ κ * a by positivity)
    nlinarith [mul_nonneg (show 0 ≤ (R : ℝ) by positivity)
      (show 0 ≤ κ * a by positivity)]
  have hTa := hTU.trans (proportionalParameter_cutoff_le_charge ha0 hs1)
  let cells : FixedCutoffInitialCellFamily s a κ δ ha hb' := fun J =>
    Classical.choice (hcells J ((mem_realInitialRows hT0 J).mp J.property))
  refine ⟨ha, hb', hU, hδb, hr a hAra, hba, hTU,
    proportionalParameter_cutoff_le_charge ha0 hs1, cells, ?_⟩
  intro j e he
  have hsum := sum_abs_fixedCutoffInitialRepairExterior_indicator_le_budget cells hδ hδb hs1 hρ
    hU hlarge hQ hba hQU (realInitialRows_card_le_charge hT0 hTa) j e he
  exact hsum.trans ((mul_le_mul_of_nonneg_right (hb a hAba) (exp_nonneg _)).trans_eq (by ring))

end GapFamily.Construction
