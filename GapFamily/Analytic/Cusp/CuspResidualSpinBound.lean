import GapFamily.Analytic.Cusp.CuspResidualSpinNorm
import GapFamily.Analytic.Cusp.CuspResidualSpinTail

noncomputable section
namespace GapFamily.Analytic
open Set CuspFourierCutoff

/-- The two actual compact-height terms admit uniform bounds on the full fixed
parameter disk; their Fourier phase does not change their Hilbert norms. -/
theorem cuspResidual_compact_terms_uniform_spin_bound :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ (1 / 8 : ℝ) →
      ‖cuspPoincareDirectRemnant J (1 / 4) (exponent κ + 2)‖ ≤ A ∧
      ‖weightedForcing J (1 / 4) κ‖ ≤ B := by
  have hrem : ContinuousOn (fun κ : ℂ =>
      cuspPoincareDirectRemnant 0 (1 / 4) (exponent κ + 2))
      (Metric.closedBall 0 (1 / 8 : ℝ)) := by
    intro κ hκ
    have hn : ‖κ‖ ≤ (1 / 8 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hκ
    have hg := cuspResidual_quarter_disk_gap hn
    have hp : 0 < (exponent κ + 2).re + (1 / 4 : ℝ) := by linarith
    have ha : AnalyticAt ℂ (fun z : ℂ =>
        cuspPoincareDirectRemnant 0 (1 / 4) (exponent z + 2)) κ :=
      (cuspPoincareDirectRemnant_analyticAt 0 (1 / 4) hp).comp_of_eq
        (show AnalyticAt ℂ (fun z : ℂ => exponent z + 2) κ by unfold exponent; fun_prop) rfl
    exact ha.continuousAt.continuousWithinAt
  have hforce : ContinuousOn (weightedForcing 0 (1 / 4))
      (Metric.closedBall 0 (1 / 8 : ℝ)) :=
    fun κ _ => (weightedForcing_analyticAt 0 (1 / 4) κ).continuousAt.continuousWithinAt
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : ℂ) (1 / 8 : ℝ)).exists_bound_of_continuousOn hrem
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (1 / 8 : ℝ)).exists_bound_of_continuousOn hforce
  refine ⟨|A| + 1, |B| + 1, by positivity, by positivity, ?_⟩
  intro J κ hκ
  have hmem : κ ∈ Metric.closedBall (0 : ℂ) (1 / 8 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hκ
  have hg := cuspResidual_quarter_disk_gap hκ
  have hp : 0 < (exponent κ + 2).re + (1 / 4 : ℝ) := by linarith
  rw [norm_cuspPoincareDirectRemnant_eq_zero_spin J (1 / 4) hp,
    norm_weightedForcing_eq_zero_spin J (1 / 4) κ]
  exact ⟨(hA κ hmem).trans (by linarith [le_abs_self A]),
    (hB κ hmem).trans (by linarith [le_abs_self B])⟩

/-- The actual quarter-weighted residual has at most quadratic spin growth,
uniformly on the complete fixed parameter disk. -/
theorem cuspPoincareResidualSource_quarter_uniform_spin_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ (1 / 8 : ℝ) →
      ‖cuspPoincareResidualSource J (1 / 4) (by norm_num) κ‖ ≤
        C * (1 + (J : ℝ) ^ 2) := by
  obtain ⟨A, hA, htail⟩ := cuspWeightedTailAnalytic_quarter_uniform_spin_bound
  obtain ⟨B, D, hB, hD, hcompact⟩ := cuspResidual_compact_terms_uniform_spin_bound
  let P : ℝ := (2 * Real.pi) ^ 2 * (A + B)
  have hP : 0 ≤ P := mul_nonneg (sq_nonneg _) (by linarith)
  refine ⟨P + D, by linarith, ?_⟩
  intro J κ hκ
  obtain ⟨hrem, hforce⟩ := hcompact J κ hκ
  calc
    ‖cuspPoincareResidualSource J (1 / 4) (by norm_num) κ‖ ≤
        (2 * Real.pi * (J : ℝ)) ^ 2 * (A + B) + D := by
      unfold cuspPoincareResidualSource
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
      exact add_le_add (mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add (htail J κ hκ) hrem))
        (sq_nonneg _)) hforce
    _ = P * (J : ℝ) ^ 2 + D := by dsimp [P]; ring
    _ ≤ (P + D) * (1 + (J : ℝ) ^ 2) := by
      nlinarith [mul_nonneg hD.le (sq_nonneg (J : ℝ))]

end GapFamily.Analytic
