import GapFamily.Analytic.Poincare.Fourier.PoincareFourierContinuation
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdModular
import GapFamily.Analytic.Modular.Geometry.ModularSeamCover

/-! Consequences of a square-root cusp bound for the actual canonical seed.
The fundamental-domain bound remains an explicit input in this module. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdHeightReduction
open Set MeasureTheory UpperHalfPlane PoincareCanonical
open PoincareFourierContinuation PoincareFourier CuspFourierCutoff
open scoped MatrixGroups

/-- Actual modular reduction transports the stated closed-domain height estimate. -/
theorem thresholdSeed_norm_le_sqrt_max_of_fd_bound
    (J : ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hfd : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd →
      ‖thresholdSeed J τ‖ ≤ C * Real.sqrt τ.im) (τ : UpperHalfPlane) :
    ‖thresholdSeed J τ‖ ≤ C * Real.sqrt (max τ.im (1 / τ.im)) := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  calc
    _ = ‖thresholdSeed J (g • τ)‖ := congrArg norm (thresholdSeed_smul J τ g).symm
    _ ≤ C * Real.sqrt (g • τ).im := hfd _ hg
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (modular_smul_im_le_max g τ)) hC

/-- At height at most one, the same actual seed is bounded by the inverse square root. -/
theorem thresholdSeed_norm_le_inv_sqrt_of_fd_bound
    (J : ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hfd : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd →
      ‖thresholdSeed J τ‖ ≤ C * Real.sqrt τ.im)
    (τ : UpperHalfPlane) (hτ : τ.im ≤ 1) :
    ‖thresholdSeed J τ‖ ≤ C / Real.sqrt τ.im := by
  have hh : τ.im ≤ 1 / τ.im := by
    apply (le_div_iff₀ τ.im_pos).mpr
    exact (mul_le_mul hτ hτ τ.im_pos.le (by norm_num)).trans_eq (one_mul 1)
  have hb := thresholdSeed_norm_le_sqrt_max_of_fd_bound J hC hfd τ
  rw [max_eq_right hh, one_div, Real.sqrt_inv, ← div_eq_mul_inv] at hb
  exact hb

/-- The ordinary Fourier integral inherits the same bound uniformly in output spin.
No fundamental-domain growth estimate is supplied by this implication. -/
theorem thresholdFourierCoefficient_norm_le_inv_sqrt_of_fd_bound
    (J : ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hfd : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd →
      ‖thresholdSeed J τ‖ ≤ C * Real.sqrt τ.im)
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) (j : ℤ) :
    ‖thresholdFourierCoefficient y hy j J‖ ≤ C / Real.sqrt y := by
  unfold thresholdFourierCoefficient
  have hpoint (x : ℝ) :
      ‖cuspFourierMode (-j) x * thresholdSeed J (rowPoint y hy x)‖ ≤
        C / Real.sqrt y := by
    rw [norm_mul, norm_cuspFourierMode, one_mul]
    exact thresholdSeed_norm_le_inv_sqrt_of_fd_bound J hC hfd (rowPoint y hy x) hy1
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (fun x _ => hpoint x)

end GapFamily.Analytic.PoincareThresholdHeightReduction
