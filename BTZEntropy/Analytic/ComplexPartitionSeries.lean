import BTZEntropy.Analytic.PartitionSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphic partition generating series

The real nonnegative coefficient sum supplies absolute convergence and local
uniform bounds for the same generating series on the complex unit disk.
-/

noncomputable section

namespace BTZEntropy

/-- The complex generating series for the actual partition multiplicity. -/
def complexPartitionSeries (q : ℂ) : ℂ :=
  ∑' n : ℕ, (partitionCount n : ℂ) * q ^ n

theorem summable_complexPartitionSeries {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => (partitionCount n : ℂ) * q ^ n) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_pow, Complex.norm_natCast] using
    summable_partitionCount_mul_pow (norm_nonneg q) hq

theorem analyticAt_complexPartitionSeries {q : ℂ} (hq : ‖q‖ < 1) :
    AnalyticAt ℂ complexPartitionSeries q := by
  obtain ⟨r, hqr, hr⟩ := exists_between hq
  have hr0 : 0 ≤ r := (norm_nonneg q).trans hqr.le
  have hd : DifferentiableOn ℂ complexPartitionSeries (Metric.ball 0 r) := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      (summable_partitionCount_mul_pow hr0 hr)
    · intro n
      exact ((differentiable_const _).mul (differentiable_id.pow n)).differentiableOn
    · exact Metric.isOpen_ball
    · intro n w hw
      have hwr : ‖w‖ ≤ r := (by
        simpa only [Metric.mem_ball, dist_zero_right] using hw : ‖w‖ < r).le
      simp only [norm_mul, norm_pow, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hwr n)
        (Nat.cast_nonneg _)
  apply hd.analyticAt
  apply Metric.isOpen_ball.mem_nhds
  simpa only [Metric.mem_ball, dist_zero_right] using hqr

end BTZEntropy
