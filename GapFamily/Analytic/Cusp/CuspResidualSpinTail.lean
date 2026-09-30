import GapFamily.Analytic.Cusp.CuspPoincareResidualSource
import GapFamily.Analytic.Cusp.CuspHeightWeightedNormal

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory CuspFourierCutoff
open scoped ENNReal

/-- The fixed parameter disk stays strictly inside the actual weighted-tail domain. -/
theorem cuspResidual_quarter_disk_gap {κ : ℂ} (hκ : ‖κ‖ ≤ (1 / 8 : ℝ)) :
    2 < (exponent κ + 2).re - (1 / 4 : ℝ) := by
  have hr := (Complex.abs_re_le_norm κ).trans hκ
  have hl := (abs_le.mp hr).1
  norm_num [exponent, Complex.add_re] at *
  linarith

/-- A single actual Hilbert norm bound controls the nonidentity tail for every
integer spin and every point of the fixed quarter-weight parameter disk. -/
theorem cuspWeightedTailAnalytic_quarter_uniform_spin_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ (1 / 8 : ℝ) →
      ‖cuspWeightedTailAnalytic J (1 / 4) (by norm_num) (exponent κ + 2)‖ ≤ C := by
  obtain ⟨u, hu, hbound⟩ := shifted_nonidentityPoincare_quarter_weight_majorant_ae
  let M : ℝ := (measureUnivNNReal modularMeasure : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
  have hmajor : Summable (fun q => M * |u q|) := hu.abs.mul_left M
  let S : ℝ := ∑' q, M * |u q|
  refine ⟨|S| + 1, by positivity, ?_⟩
  intro J κ hκ
  have hgap := cuspResidual_quarter_disk_gap hκ
  have hpos : (1 / 4 : ℝ) < (exponent κ + 2).re := by linarith
  have hshift : exponent κ + 2 = (5 / 2 : ℂ) + κ := by unfold exponent; ring
  have hnorm (q : {q : CuspCoset // q ≠ identityCuspCoset}) :
      ‖cuspWeightedTailAnalyticTerm J (1 / 4) (by norm_num) q (exponent κ + 2)‖ ≤
        M * |u q| := by
    apply Lp.norm_le_of_ae_bound (abs_nonneg (u q))
    filter_upwards [cuspWeightedTailAnalyticTerm_ae J (1 / 4) (by norm_num) q hpos,
      hbound] with τ hrep hb
    rw [hrep, cuspWeightedTailTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg τ.im_pos.le (1 / 4 : ℝ)), hshift]
    exact (hb J q κ hκ).trans (le_abs_self _)
  have hs := summable_norm_cuspWeightedTailAnalyticTerm J (1 / 4) (by norm_num) hgap
  calc
    ‖cuspWeightedTailAnalytic J (1 / 4) (by norm_num) (exponent κ + 2)‖ ≤
        ∑' q, ‖cuspWeightedTailAnalyticTerm J (1 / 4) (by norm_num) q (exponent κ + 2)‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ S := Summable.tsum_le_tsum hnorm hs hmajor
    _ ≤ |S| + 1 := by linarith [le_abs_self S]

end GapFamily.Analytic
