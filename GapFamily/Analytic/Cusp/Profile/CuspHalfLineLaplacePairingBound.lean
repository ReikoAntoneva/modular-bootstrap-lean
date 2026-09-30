import GapFamily.Analytic.Cusp.Profile.CuspHalfLineLaplace

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory CuspHalfLineLaplace

/-- The actual ordinary complex-bilinear L² pairing has norm at most the
norm of its first argument; no conjugation is inserted. -/
theorem cuspHalfLineLaplace_lpPairing_norm_le (g : HalfLineL2) :
    ‖(ContinuousLinearMap.mul ℂ ℂ).lpPairing
      (volume.restrict (Ioi (0 : ℝ))) 2 2 g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro f
  change ‖L1.integralCLM' ℂ ((ContinuousLinearMap.mul ℂ ℂ).holder 1 g f)‖ ≤ ‖g‖ * ‖f‖
  rw [← L1.integral_eq' ℂ]
  calc
    _ ≤ ‖(ContinuousLinearMap.mul ℂ ℂ).holder 1 g f‖ := L1.norm_integral_le _
    _ ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖g‖ * ‖f‖ :=
      ContinuousLinearMap.norm_holder_apply_apply_le _ g f
    _ ≤ 1 * ‖g‖ * ‖f‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℂ ℂ
    _ = ‖g‖ * ‖f‖ := by rw [one_mul]

end GapFamily.Analytic
