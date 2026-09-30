import GapFamily.Construction.ProportionalParameter
import GapFamily.Construction.RealFixedCutoffInitialCell

/-!
# Initial cell with an independently fixed marker

The auxiliary integers are fixed before the real gap ratio. Every sufficiently
large real vacuum shift supplies cells for the actual transferred reference
with marker `δ`.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- Every fixed nonnegative marker eventually lies below the growing reference
cutoff. The transferred reference supplies all actual initial cells for
every sufficiently large real vacuum shift. -/
theorem exists_fixedCutoff_initial_reference_cell {R s : ℕ}
    (hR : 16 * fixedCutoffReferenceRadius ≤ R)
    (hC : fixedCutoffReferenceNegativeExponent ≤ sqrt (R : ℝ)) (hs : 1 ≤ s)
    {κ : ℝ} (hκpos : 0 < κ) (hκ : κ ≤ 1 / (4 * R * (s : ℝ) ^ 2))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a →
      ∃ (ha : 2 ≤ a) (hb : 1 ≤ κ * a),
      δ ≤ κ * a ∧
      ∀ j : ℤ, |(j : ℝ)| ≤ (fixedCutoffReferenceRadius : ℝ) * (κ * a) →
      Nonempty (InitialReferenceCell j (max (κ * a) |(j : ℝ)|)
        (proportionalCutoff a s)
        (proportionalDegree a s)
        (fixedCutoffReferenceDensity a
          (κ * a) δ ha hb j)) := by
  have hR1 : 1 ≤ R := by have := fixedCutoffReferenceRadius_gt_six; omega
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hRr : 16 * (fixedCutoffReferenceRadius : ℝ) ≤ R := by exact_mod_cast hR
  have hR1r : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hκone : κ ≤ 1 := by
    have hden : 1 ≤ 4 * (R : ℝ) * (s : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((s : ℝ) - 1)]
    exact hκ.trans (by simpa using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden)
  obtain ⟨k₀, hk₀⟩ := exists_realFixedCutoffInitialCell_threshold
    (D := 2 * (s : ℝ) + 1) (by positivity)
  let V : ℝ := max 16 (2 / (π ^ 4 / 625) + 1)
  let A : ℝ := max 2 (max ((s : ℝ) ^ 2 * V)
    ((fixedCutoffReferenceBandThreshold : ℝ) / κ))
  obtain ⟨aδ, haδ1, haδ⟩ := exists_proportionalParameter_gap_threshold hκpos δ
  let a₀ : ℝ := max (max ((s : ℝ) * ((k₀ : ℝ) + 2)) A) aδ
  refine ⟨a₀, ?_, ?_⟩
  · exact haδ1.trans (le_max_right _ _)
  intro a haa
  have hA : max 2 (max ((s : ℝ) ^ 2 * V)
      ((fixedCutoffReferenceBandThreshold : ℝ) / κ)) ≤ a :=
    (le_max_right _ _).trans ((le_max_left _ _).trans haa)
  have hδb := haδ a ((le_max_right _ _).trans haa)
  have ha : 2 ≤ a := (le_max_left _ _).trans hA
  have ha0 : 0 ≤ a := by linarith
  have hnb : (fixedCutoffReferenceBandThreshold : ℝ) ≤ κ * a := by
    have hdiv := (le_max_right _ _).trans ((le_max_right _ _).trans hA)
    have hm := (div_le_iff₀ hκpos).mp hdiv
    nlinarith
  have hb : 1 ≤ κ * a := by
    have ht : (100 : ℝ) ≤ fixedCutoffReferenceBandThreshold := by
      exact_mod_cast fixedCutoffReferenceBandThreshold_ge_hundred
    linarith
  have hba : κ * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right hκone ha0
  have hUV : V ≤ proportionalCutoff a s := by
    unfold proportionalCutoff
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (s : ℝ) ^ 2)).mpr
    nlinarith [(le_max_left _ _).trans ((le_max_right _ _).trans hA)]
  have hU : 16 ≤ proportionalCutoff a s :=
    (le_max_left _ _).trans hUV
  have hlarge : 2 / (π ^ 4 / 625) < proportionalCutoff a s := by
    have h := (le_max_right _ _).trans hUV
    linarith
  have hgap := proportionalParameter_gap_le_cutoff ha0 hR1 hs hκ
  have hTU : (fixedCutoffReferenceRadius : ℝ) * (κ * a) ≤
      proportionalCutoff a s / 16 := by
    have hm := (le_div_iff₀ (show 0 < 4 * (R : ℝ) by positivity)).mp hgap
    have hb0 : 0 ≤ κ * a := by positivity
    have hscale := mul_le_mul_of_nonneg_right hRr hb0
    nlinarith [mul_nonneg (show 0 ≤ (R : ℝ) by positivity) hb0]
  obtain ⟨hk, hcharge⟩ := proportionalParameter_degree_threshold hs k₀ a
    ((le_max_left _ _).trans ((le_max_left _ _).trans haa))
  refine ⟨ha, hb, hδb, ?_⟩
  apply hk₀ _ hk _ _ _ _ ha hb hδ hδb hnb hba hU hlarge hTU
    (proportionalParameter_polynomial_base_le hs)
    (proportionalParameter_negative_exponent_le ha0 hR1 hs hC hκ hcharge)
    (proportionalParameter_degree_le_sqrt_aU ha0 s)

end GapFamily.Construction
