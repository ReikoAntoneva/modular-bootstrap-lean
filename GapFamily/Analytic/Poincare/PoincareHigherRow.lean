import GapFamily.Analytic.Poincare.PoincareAnalytic

noncomputable section

namespace GapFamily.Analytic.PoincareHigherRow

open Set
open scoped MatrixGroups

/-- Dividing by an ordinary positive height power preserves an upper bound,
with the explicit lower-height constant. -/
theorem div_height_pow_le {x u y B : ℝ} (hx : 0 ≤ x) (hB : 0 < B)
    (hBy : B ≤ y) (hxu : x ≤ u) (n : ℕ) :
    x / y ^ n ≤ (B ^ n)⁻¹ * u := by
  calc
    x / y ^ n ≤ x / B ^ n := div_le_div_of_nonneg_left hx (pow_pos hB n)
      (pow_le_pow_left₀ hB.le hBy n)
    _ ≤ u / B ^ n := div_le_div_of_nonneg_right hxu (pow_nonneg hB.le n)
    _ = _ := by ring

/-- The explicit original integer-row power remains a majorant after dividing
by any fixed ordinary source-height power. -/
theorem cusp_height_rpow_div_pow_le_of_mem_verticalStrip (n : ℕ)
    {A B Y σ : ℝ} (hB : 0 < B) (hσ : 0 ≤ σ) {τ : UpperHalfPlane}
    (hτ : τ ∈ UpperHalfPlane.verticalStrip A B) (hY : τ.im ≤ Y) (q : CuspCoset) :
    (q.out • τ).im ^ σ / τ.im ^ n ≤
      ((Y ^ σ * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * σ))) / B ^ n) *
        ‖cuspBottomRow q‖ ^ (-(2 * σ)) := by
  have hh := cusp_height_rpow_le_of_mem_verticalStrip hB hσ hτ hY q
  have hd : B ^ n ≤ τ.im ^ n := pow_le_pow_left₀ hB.le hτ.2 n
  calc
    _ ≤ ((Y ^ σ * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * σ))) *
        ‖cuspBottomRow q‖ ^ (-(2 * σ))) / B ^ n :=
      div_le_div₀ ((Real.rpow_nonneg (q.out • τ).im_pos.le σ).trans hh)
        hh (pow_pos hB n) hd
    _ = _ := mul_div_right_comm _ _ _

/-- The original compact height majorant supplies the same image-height bound
and a summable inverse-source-height majorant at every fixed derivative order. -/
theorem exists_compact_height_power_div_majorant (n : ℕ) {σ : ℝ}
    (hσ : 1 < σ) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ M : ℝ, 0 < M ∧ ∃ u : CuspCoset → ℝ,
      Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (τ : UpperHalfPlane), τ ∈ K →
        (q.out • τ).im ≤ M ∧ (q.out • τ).im ^ σ / τ.im ^ n ≤ u q := by
  obtain ⟨M, hM, u, hu, hu0, hub⟩ := exists_cusp_height_compact_majorant hK hσ
  obtain ⟨A, B, hB, hstrip⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  refine ⟨M, hM, fun q => (B ^ n)⁻¹ * u q, hu.mul_left _,
    fun q => mul_nonneg (inv_nonneg.mpr (pow_nonneg hB.le n)) (hu0 q), ?_⟩
  intro q τ hτ
  exact ⟨(hub q τ hτ).1,
    div_height_pow_le (Real.rpow_nonneg (q.out • τ).im_pos.le σ) hB
      (hstrip hτ).2 (hub q τ hτ).2 n⟩

/-- A bounded exponent strip inside the actual convergence region has one
summable majorant and one image-height bound at every fixed derivative order. -/
theorem exists_compact_height_power_div_majorant_strip (n : ℕ) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ M : ℝ, 0 < M ∧ ∃ u : CuspCoset → ℝ,
      Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (σ : ℝ) (τ : UpperHalfPlane),
        a ≤ σ → σ ≤ b → τ ∈ K →
          (q.out • τ).im ≤ M ∧ (q.out • τ).im ^ σ / τ.im ^ n ≤ u q := by
  obtain ⟨M, hM, u, hu, hu0, hub⟩ := exists_cusp_height_compact_majorant hK ha
  obtain ⟨_, _, v, hv, hv0, hvb⟩ := exists_cusp_height_compact_majorant hK (ha.trans_le hab)
  obtain ⟨A, B, hB, hstrip⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  refine ⟨M, hM, fun q => (B ^ n)⁻¹ * (u q + v q), (hu.add hv).mul_left _,
    fun q => mul_nonneg (inv_nonneg.mpr (pow_nonneg hB.le n)) (add_nonneg (hu0 q) (hv0 q)), ?_⟩
  intro q σ τ hσa hσb hτ
  have hp : (q.out • τ).im ^ σ ≤ u q + v q :=
    (rpow_le_add_endpoint (q.out • τ).im_pos hσa hσb).trans
      (add_le_add (hub q τ hτ).2 (hvb q τ hτ).2)
  exact ⟨(hub q τ hτ).1,
    div_height_pow_le (Real.rpow_nonneg (q.out • τ).im_pos.le σ) hB
      (hstrip hτ).2 hp n⟩

end GapFamily.Analytic.PoincareHigherRow
