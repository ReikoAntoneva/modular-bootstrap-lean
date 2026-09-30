import BTZEntropy.Analytic.SaddleEntropyUniform

/-! Transfer comparison errors normalized by the explicit Gaussian saddle
scale to errors relative to the actual reference count. -/

noncomputable section

open Set Filter

namespace BTZEntropy

universe u

theorem relative_error_le_of_scale {N R S : ℝ} (hS : 0 < S)
    (hclose : |R / S - 1| ≤ 1 / 2) :
    |N / R - 1| ≤ 2 * |(N - R) / S| := by
  have hr : 1 / 2 ≤ R / S := by have := (abs_le.mp hclose).1; linarith
  have hR : 0 < R := (div_pos_iff_of_pos_right hS).mp (by linarith)
  have hRS : S ≤ 2 * R := by
    have := (le_div_iff₀ hS).mp hr
    linarith
  have hid : N / R - 1 = (N - R) / R := by field_simp
  rw [hid, abs_div, abs_of_pos hR, abs_div, abs_of_pos hS]
  apply (div_le_iff₀ hR).2
  have hcancel : |N - R| / S * S = |N - R| := div_mul_cancel₀ _ hS.ne'
  have hmul := mul_le_mul_of_nonneg_left hRS
    (div_nonneg (abs_nonneg (N - R)) hS.le)
  calc
    _ = |N - R| / S * S := hcancel.symm
    _ ≤ |N - R| / S * (2 * R) := hmul
    _ = _ := by ring

theorem saddleCount_eventually_close_to_scale
    (φ : SmoothKernel) (reference : ℝ → ℝ → ℝ)
    (hexp : UniformSaddleCountExpansion φ reference)
    (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a, a₀ ≤ a → ∀ x ∈ Icc L U,
      |reference x (GapFamily.gapFamilyCharge a) /
          saddleCountScale φ x (GapFamily.gapFamilyCharge a) - 1| ≤ 1 / 2 := by
  obtain ⟨D, hD, c₀, hc₀, h⟩ := hexp 0 L U hL hLU
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (GapFamily.tendsto_gapFamilyCharge_atTop.eventually_ge_atTop (max c₀ (2 * D)))
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  intro a ha x hx
  have hc := hN a ((le_max_right _ _).trans ha)
  have hcpos : 0 < GapFamily.gapFamilyCharge a :=
    lt_of_lt_of_le zero_lt_one (hc₀.trans ((le_max_left _ _).trans hc))
  have he := h _ ((le_max_left _ _).trans hc) x hx
  simp only [countCorrectionPolynomial, Finset.range_zero, Finset.sum_empty,
    Polynomial.eval_zero, add_zero, zero_add, pow_one] at he
  refine he.trans ((div_le_iff₀ hcpos).2 ?_)
  have := (le_max_right c₀ (2 * D)).trans hc
  linarith

theorem uniformRelativeMatching_of_saddleScale_error
    {ι : Type u} {B : ℝ} {selectors : Set ι}
    {family : ι → ℝ → ℝ → GapFamily.Spectrum}
    (φ : SmoothKernel) (reference : ℝ → ℝ → ℝ)
    (hexp : UniformSaddleCountExpansion φ reference)
    (herr : ∀ q : ℕ, 1 ≤ q → UniformRemainder B selectors q
      (fun σ a δ x =>
        (smoothCount φ (GapFamily.gapFamilyCharge a) (family σ a δ)
          (x * GapFamily.gapFamilyCharge a) - reference x (GapFamily.gapFamilyCharge a)) /
            saddleCountScale φ x (GapFamily.gapFamilyCharge a))) :
    UniformRelativeMatching B selectors family φ
      (fun a x => reference x (GapFamily.gapFamilyCharge a)) := by
  refine ⟨uniformReferencePositive_of_saddleCountExpansion φ reference hexp, ?_⟩
  intro q hq L U hL hLU
  obtain ⟨C, hC, N, hN, he⟩ := herr q hq L U hL hLU
  obtain ⟨M, hM, hm⟩ := saddleCount_eventually_close_to_scale φ reference hexp L U hL hLU
  refine ⟨2 * C, mul_pos (by norm_num) hC, max N M,
    hN.trans (le_max_left _ _), ?_⟩
  intro σ hσ a ha δ hδ x hx
  have haN : N ≤ a := (le_max_left _ _).trans ha
  have haM : M ≤ a := (le_max_right _ _).trans ha
  have hc : 0 < GapFamily.gapFamilyCharge a :=
    zero_lt_one.trans (GapFamily.gapFamilyCharge_gt_one (zero_lt_one.trans_le (hN.trans haN)))
  have hS := saddleCountScale_pos φ (hL.trans_le hx.1) hc
  calc
    _ ≤ 2 * |(smoothCount φ (GapFamily.gapFamilyCharge a) (family σ a δ)
          (x * GapFamily.gapFamilyCharge a) - reference x (GapFamily.gapFamilyCharge a)) /
            saddleCountScale φ x (GapFamily.gapFamilyCharge a)| :=
      relative_error_le_of_scale hS (hm a haM x hx)
    _ ≤ 2 * (C / GapFamily.gapFamilyCharge a ^ q) :=
      mul_le_mul_of_nonneg_left (he σ hσ a haN δ hδ x hx) (by norm_num)
    _ = (2 * C) / GapFamily.gapFamilyCharge a ^ q := by ring

end BTZEntropy
