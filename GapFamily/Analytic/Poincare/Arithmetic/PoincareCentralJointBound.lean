import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdFundamentalBound
import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralBaseBound
import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralSelberg

/-! Unconditional normalized and joint bounds for the actual canonical
threshold central-zeta values. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCentralZeta

/-- The proved fundamental-domain estimate for the actual spin-one threshold
seed supplies one positive constant for all nonzero normalized frequencies. -/
theorem exists_centralZeta_zero_base_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℤ, N ≠ 0 →
      ‖centralZeta N 1 0‖ ≤ C * |(N : ℝ)| := by
  obtain ⟨C, hC, hfd⟩ :=
    PoincareThresholdFundamentalBound.exists_thresholdSeed_one_fd_bound
  exact exists_centralZeta_base_bound_of_threshold_fd_bound hC.le hfd

/-- The actual central Selberg identity gives a single positive constant,
uniform over both nonzero signed frequencies, without an estimate or
continuation premise. -/
theorem exists_centralZeta_zero_joint_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ j J : ℤ, j ≠ 0 → J ≠ 0 →
      ‖centralZeta j J 0‖ ≤ C * |(j : ℝ) * (J : ℝ)| :=
  exists_uniform_centralZeta_zero_bound exists_centralZeta_zero_base_bound

end GapFamily.Analytic.PoincareCentralZeta
