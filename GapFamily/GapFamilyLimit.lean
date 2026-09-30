import GapFamily.GapFamilyContract
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Limit and choice interface for real gap families

An eventual supply of spectra at every sufficiently large real shift gives
a total real-parameter family. Its exact gap determines the required limits.
-/

noncomputable section

open Filter

namespace GapFamily

theorem tendsto_gapFamilyCharge_atTop : Tendsto gapFamilyCharge atTop atTop := by
  exact tendsto_atTop_add_const_right atTop 1
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 12))

theorem tendsto_fixedGap_ratio_zero (δ : ℝ) :
    Tendsto (fun a : ℝ => δ / a) atTop (nhds 0) := by
  simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul δ

theorem tendsto_proportionalGap_dimension_ratio (κ : ℝ) :
    Tendsto (fun a : ℝ => (a + κ * a) / gapFamilyCharge a)
      atTop (nhds ((1 + κ) / 12)) := by
  have hlim : Tendsto (fun a : ℝ => (1 + κ) / (12 + a⁻¹))
      atTop (nhds ((1 + κ) / 12)) := by
    have hnum : Tendsto (fun _ : ℝ => (1 + κ)) atTop (nhds (1 + κ)) :=
      tendsto_const_nhds
    have hden : Tendsto (fun a : ℝ => 12 + a⁻¹) atTop (nhds 12) := by
      simpa using tendsto_inv_atTop_zero.const_add (12 : ℝ)
    exact hnum.div hden (by norm_num)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  have ha0 : 0 < a := by linarith
  have hc : gapFamilyCharge a ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) (gapFamilyCharge_gt_one ha0))
  unfold gapFamilyCharge at hc ⊢
  field_simp

theorem proportionalGap_ratio_gt_threshold {κ : ℝ} (hκ : 0 < κ) :
    (1 : ℝ) / 12 < (1 + κ) / 12 := by
  linarith

/-- Classical choice extends an eventual supply of spectra to a total real
family. No spectral condition is required below its positive threshold. -/
theorem exists_gapFamily_of_eventually_realizesGap (g : ℝ → ℝ)
    (h : ∀ᶠ a in atTop, ∃ s : Spectrum, RealizesGap a (g a) s) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∃ family : ℝ → Spectrum,
      ∀ a, a₀ ≤ a → RealizesGap a (g a) (family a) := by
  classical
  obtain ⟨A, hA⟩ := eventually_atTop.1 h
  have hex : ∀ a : ℝ, ∃ s : Spectrum, max A 1 ≤ a → RealizesGap a (g a) s := by
    intro a
    by_cases ha : max A 1 ≤ a
    · obtain ⟨s, hs⟩ := hA a ((le_max_left A 1).trans ha)
      exact ⟨s, fun _ => hs⟩
    · exact ⟨⟨∅, fun _ => 0⟩, fun hcontra => (ha hcontra).elim⟩
  choose family hfamily using hex
  exact ⟨max A 1, le_max_right A 1, family, hfamily⟩

/-- The exact eventual real spectra imply all quantifiers and the normalized
first-dimension limit in part (i). -/
theorem proportionalGapFamilyExists_of_eventually_realizesGap
    (h : ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ < κ₀ →
      ∀ᶠ a in atTop, ∃ s : Spectrum, RealizesGap a (κ * a) s) :
    ProportionalGapFamilyExists := by
  obtain ⟨κ₀, hκ₀, h⟩ := h
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ hκlt
  obtain ⟨a₀, ha₀, family, hf⟩ :=
    exists_gapFamily_of_eventually_realizesGap _ (h κ hκ hκlt)
  refine ⟨a₀, ha₀, family, hf, ?_, proportionalGap_ratio_gt_threshold hκ⟩
  apply (tendsto_proportionalGap_dimension_ratio κ).congr'
  filter_upwards [eventually_ge_atTop a₀] with a ha
  rw [(hf a ha).firstDimension_eq]

/-- The fixed shifted gap is eventually exactly `δ`, including at the
threshold `δ = 0`; its quotient by the real shift tends to zero. -/
theorem fixedGapFamilyExists_of_eventually_realizesGap
    (h : ∀ δ : ℝ, 0 ≤ δ →
      ∀ᶠ a in atTop, ∃ s : Spectrum, RealizesGap a δ s) :
    FixedGapFamilyExists := by
  intro δ hδ
  obtain ⟨a₀, ha₀, family, hf⟩ :=
    exists_gapFamily_of_eventually_realizesGap (fun _ => δ) (h δ hδ)
  refine ⟨a₀, ha₀, family, hf, ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop a₀] with a ha
    exact (hf a ha).firstShiftedEnergy_eq.symm
  · apply (tendsto_fixedGap_ratio_zero δ).congr'
    filter_upwards [eventually_ge_atTop a₀] with a ha
    rw [(hf a ha).firstShiftedEnergy_eq]

end GapFamily
