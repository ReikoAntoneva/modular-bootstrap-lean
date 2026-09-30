import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralFactorBound
import GapFamily.Analytic.Poincare.PoincareFrequencyHeight

noncomputable section
namespace GapFamily.Analytic.PoincareCentralFactor
open Set BesselCoshOrder

/-- At the actual frequency-dependent height, one fixed small order disk gives a
uniform central-factor bound and reciprocal estimate with the exact frequency powers. -/
theorem exists_centralFourierFactor_frequency_bounds :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ j : ℤ, j ≠ 0 → ∀ κ : ℂ, ‖κ‖ ≤ δ →
        centralFourierFactor (frequencyHeight j) j κ ≠ 0 ∧
        ‖centralFourierFactor (frequencyHeight j) j κ‖ ≤
          C * Real.sqrt (frequencyHeight j) * |(j : ℝ)| ^ κ.re ∧
        ‖(centralFourierFactor (frequencyHeight j) j κ)⁻¹‖ ≤
          C * Real.sqrt (1 + |(j : ℝ)|) * |(j : ℝ)| ^ (-κ.re) := by
  obtain ⟨δ, hδ, hδsmall, C, hC, hbound⟩ := exists_centralBesselOn_closedBall_bounds
  refine ⟨δ, hδ, hδsmall, C, hC, ?_⟩
  intro j hj κ hκ
  have hy := frequencyHeight_pos j
  have ht := frequencyHeight_argument_mem hj
  obtain ⟨hnon, hup, hinv⟩ := hbound κ hκ _ ht
  have hnp : 0 < |(j : ℝ)| := lt_of_lt_of_le zero_lt_one (one_le_abs_frequency hj)
  have hpow : ((|(j : ℝ)| : ℝ) : ℂ) ^ κ ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hnp.ne'))
  have hsq : (Real.sqrt (frequencyHeight j) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  have he : centralFourierFactor (frequencyHeight j) j κ =
      (((|(j : ℝ)| : ℝ) : ℂ) ^ κ * (Real.sqrt (frequencyHeight j) : ℂ)) *
        (centralGammaFactor κ * besselK κ
          (2 * Real.pi * |(j : ℝ)| * frequencyHeight j)) := by
    unfold centralFourierFactor
    ring
  rw [he]
  refine ⟨mul_ne_zero (mul_ne_zero hpow hsq) hnon, ?_, ?_⟩
  · rw [norm_mul, norm_mul, norm_frequency_cpow hj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (|(j : ℝ)| ^ κ.re * Real.sqrt (frequencyHeight j)) * C :=
        mul_le_mul_of_nonneg_left hup (by positivity)
      _ = _ := by ring
  · rw [mul_inv, mul_inv, norm_mul, norm_mul, norm_inv_frequency_cpow hj,
      norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_sqrt_frequencyHeight]
    calc
      _ ≤ (|(j : ℝ)| ^ (-κ.re) * Real.sqrt (1 + |(j : ℝ)|)) * C :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring

end GapFamily.Analytic.PoincareCentralFactor
