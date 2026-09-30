import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroResolvent

/-! # Contraction of the actual constrained weak response

The actual weak energy equation and Cauchy–Schwarz give the operator bound,
without a density or coercivity premise.
-/

noncomputable section
namespace GapFamily.Analytic

theorem cuspMeanZeroWeakResolvent_norm_le_one : ‖cuspMeanZeroWeakResolvent‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have heq := cuspMeanZeroWeakSolution_equation f (cuspMeanZeroWeakSolution f)
  rw [← cuspMeanZeroWeakResolvent_apply] at heq
  have hre := congrArg Complex.re heq
  rw [Complex.add_re] at hre
  change RCLike.re (inner ℂ (cuspMeanZeroGradient (cuspMeanZeroWeakSolution f))
    (cuspMeanZeroGradient (cuspMeanZeroWeakSolution f))) +
    RCLike.re (inner ℂ (cuspMeanZeroWeakResolvent f) (cuspMeanZeroWeakResolvent f)) =
    RCLike.re (inner ℂ f (cuspMeanZeroWeakResolvent f)) at hre
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at hre
  have hc := re_inner_le_norm (𝕜 := ℂ) f (cuspMeanZeroWeakResolvent f)
  have hg := sq_nonneg ‖cuspMeanZeroGradient (cuspMeanZeroWeakSolution f)‖
  have hf := norm_nonneg f
  have hr := norm_nonneg (cuspMeanZeroWeakResolvent f)
  simpa only [one_mul] using (show ‖cuspMeanZeroWeakResolvent f‖ ≤ ‖f‖ by nlinarith)


end GapFamily.Analytic
