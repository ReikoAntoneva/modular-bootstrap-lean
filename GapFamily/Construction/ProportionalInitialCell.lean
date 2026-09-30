import GapFamily.Construction.ProportionalParameter
import GapFamily.Construction.RealCanonicalInitialCell

/-!
# Initial cells for every sufficiently small real proportional gap

The auxiliary integers are fixed before the real gap ratio. The vacuum
shift ranges over every sufficiently large real parameter.
The resulting cells belong to the actual canonical marker reference.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The proportional real parameter choice supplies every actual initial
cell at every sufficiently large real charge. Only the threshold depends on
the fixed positive ratio; the radius and moment ratio precede that choice. -/
theorem exists_proportional_initial_reference_cell {R s : ℕ}
    (hR : 16 * markerReferenceRadius ≤ R)
    (hC : markerReferenceNegativeExponent ≤ sqrt (R : ℝ)) (hs : 1 ≤ s)
    {κ : ℝ} (hκpos : 0 < κ) (hκ : κ ≤ 1 / (4 * R * (s : ℝ) ^ 2)) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a →
      ∃ (ha : 2 ≤ a) (hb : 1 ≤ κ * a),
      ∀ j : ℤ, |(j : ℝ)| ≤ (markerReferenceRadius : ℝ) * (κ * a) →
      Nonempty (InitialReferenceCell j (max (κ * a) |(j : ℝ)|)
        (proportionalCutoff a s)
        (proportionalDegree a s)
        (canonicalMarkerReferenceDensity a
          (κ * a) ha hb j)) := by
  have hR1 : 1 ≤ R := by have := markerReferenceRadius_gt_three; omega
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hRr : 16 * (markerReferenceRadius : ℝ) ≤ R := by exact_mod_cast hR
  have hR1r : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hκone : κ ≤ 1 := by
    have hden : 1 ≤ 4 * (R : ℝ) * (s : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((s : ℝ) - 1)]
    exact hκ.trans (by simpa using
      one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hden)
  obtain ⟨k₀, hk₀⟩ := exists_realCanonicalInitialCell_threshold
    (D := 2 * (s : ℝ) + 1) (by positivity)
  let V : ℝ := max 16 (2 / (π ^ 4 / 625) + 1)
  let A : ℝ := max 2 (max ((s : ℝ) ^ 2 * V)
    ((markerReferenceBandThreshold : ℝ) / κ))
  let a₀ : ℝ := max ((s : ℝ) * ((k₀ : ℝ) + 2)) A
  refine ⟨a₀, ?_, ?_⟩
  · have hA1 : 1 ≤ A := (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    exact hA1.trans (le_max_right _ _)
  intro a ha₀
  have hA : max 2 (max ((s : ℝ) ^ 2 * V)
      ((markerReferenceBandThreshold : ℝ) / κ)) ≤ a :=
    (le_max_right _ _).trans ha₀
  have ha : 2 ≤ a := (le_max_left _ _).trans hA
  have ha0 : 0 ≤ a := by linarith
  have hnb : (markerReferenceBandThreshold : ℝ) ≤ κ * a := by
    have hdiv := (le_max_right _ _).trans ((le_max_right _ _).trans hA)
    have hm := (div_le_iff₀ hκpos).mp hdiv
    nlinarith
  have hb : 1 ≤ κ * a := by
    have ht : (100 : ℝ) ≤ markerReferenceBandThreshold := by
      exact_mod_cast markerReferenceBandThreshold_ge_hundred
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
  have hTU : (markerReferenceRadius : ℝ) * (κ * a) ≤
      proportionalCutoff a s / 16 := by
    have hm := (le_div_iff₀ (show 0 < 4 * (R : ℝ) by positivity)).mp hgap
    have hb0 : 0 ≤ κ * a := by positivity
    have hscale := mul_le_mul_of_nonneg_right hRr hb0
    nlinarith [mul_nonneg (show 0 ≤ (R : ℝ) by positivity) hb0]
  obtain ⟨hk, hcharge⟩ := proportionalParameter_degree_threshold hs k₀ a
    ((le_max_left _ _).trans ha₀)
  refine ⟨ha, hb, ?_⟩
  apply hk₀ _ hk _ _ _ ha hb hnb hba hU hlarge hTU
    (proportionalParameter_polynomial_base_le hs)
    (proportionalParameter_negative_exponent_le ha0 hR1 hs hC hκ hcharge)
    (proportionalParameter_degree_le_sqrt_aU ha0 s)

/-- One positive interval of real gap ratios works after fixing the common
auxiliary radius. The ratio parameter `s` can still be enlarged to satisfy
the separate finite-repair error budget. -/
theorem exists_proportional_initial_reference_parameter :
    ∃ R : ℕ, 1 ≤ R ∧ 16 * markerReferenceRadius ≤ R ∧
      markerReferenceNegativeExponent ≤ sqrt (R : ℝ) ∧
      ∀ s : ℕ, 1 ≤ s → ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ κ : ℝ, 0 < κ → κ < κ₀ →
      ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a : ℝ, a₀ ≤ a →
      ∃ (ha : 2 ≤ a) (hb : 1 ≤ κ * a),
      ∀ j : ℤ, |(j : ℝ)| ≤ (markerReferenceRadius : ℝ) * (κ * a) →
      Nonempty (InitialReferenceCell j (max (κ * a) |(j : ℝ)|)
        (proportionalCutoff a s)
        (proportionalDegree a s)
        (canonicalMarkerReferenceDensity a
          (κ * a) ha hb j)) := by
  obtain ⟨R, hR1, hR, hC⟩ := exists_initialParameter_radius markerReferenceRadius
    markerReferenceNegativeExponent markerReferenceNegativeExponent_pos.le
  refine ⟨R, hR1, hR, hC, ?_⟩
  intro s hs
  refine ⟨1 / (4 * R * (s : ℝ) ^ 2), by positivity, ?_⟩
  intro κ hκpos hκ
  exact exists_proportional_initial_reference_cell hR hC hs hκpos hκ.le

end GapFamily.Construction
