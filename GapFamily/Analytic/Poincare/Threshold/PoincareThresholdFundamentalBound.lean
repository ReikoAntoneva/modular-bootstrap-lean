import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdCuspBound
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdModular
import GapFamily.Analytic.Modular.Geometry.ModularSeamCover

/-! Compact low-height completion for the actual canonical input-spin-one seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdFundamentalBound
open Set UpperHalfPlane PoincareCanonical

/-- The actual continuous low part needs no separate representative or estimate. -/
theorem exists_thresholdSeed_one_fd_bound_of_high
    (hhigh : ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane,
      |τ.re| ≤ 1 / 2 → 2 ≤ τ.im → ‖thresholdSeed 1 τ‖ ≤ C * Real.sqrt τ.im) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd →
      ‖thresholdSeed 1 τ‖ ≤ C * Real.sqrt τ.im := by
  obtain ⟨Ch, hCh, hhigh⟩ := hhigh
  obtain ⟨A, hA⟩ := (ModularGroup.isCompact_truncatedFundamentalDomain (2 : ℝ)).exists_bound_of_continuousOn
    (continuous_thresholdSeed (1 : ℤ)).continuousOn
  let C : ℝ := 2 * (|A| + Ch + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hChC : Ch ≤ C := by dsimp [C]; nlinarith [abs_nonneg A]
  refine ⟨C, hC, ?_⟩
  intro τ hτ
  by_cases hy : τ.im ≤ 2
  · have hlow : (1 / 2 : ℝ) ≤ τ.im := by
      have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
      nlinarith [τ.im_pos]
    have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt τ.im := by
      nlinarith [Real.sq_sqrt τ.im_pos.le, Real.sqrt_nonneg τ.im]
    have ha : ‖thresholdSeed 1 τ‖ ≤ A := hA τ ⟨hτ, hy⟩
    have hb := mul_le_mul_of_nonneg_left hsqrt hC.le
    have hc : A ≤ C / 2 := by dsimp [C]; nlinarith [le_abs_self A]
    exact ha.trans (by nlinarith)
  · exact (hhigh τ hτ.2 (le_of_not_ge hy)).trans
      (mul_le_mul_of_nonneg_right hChC (Real.sqrt_nonneg τ.im))

/-- A proved, uniform square-root height bound for the actual canonical spin-one seed
on the complete closed modular fundamental domain, including its seams. -/
theorem exists_thresholdSeed_one_fd_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd →
      ‖thresholdSeed 1 τ‖ ≤ C * Real.sqrt τ.im :=
  exists_thresholdSeed_one_fd_bound_of_high
    PoincareThresholdCuspBound.exists_thresholdSeed_one_high_bound

end GapFamily.Analytic.PoincareThresholdFundamentalBound
