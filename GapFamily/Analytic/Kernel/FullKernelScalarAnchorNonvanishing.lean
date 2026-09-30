import GapFamily.Analytic.Kernel.FullKernelScalarAnchorResponse
import GapFamily.Analytic.Foundation.ThresholdAnchorNonvanishing

/-! Nonvanishing of the normalization for the actual scalar inverse response.
Only invertibility of the actual low-band operator is required here. -/

noncomputable section

open Real Metric Set

namespace GapFamily.Analytic

/-- The actual high-band normalization is strictly positive. The entire
response takes value minus one at zero, so propagation rules out its
vanishing on the observation interval. -/
theorem scalarAnchorSquareMass_actual_pos {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) :
    0 < scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B hB.le) := by
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : ℂ) 16384).exists_bound_of_continuousOn
    (differentiable_scalarAnchorResponseHol J B hB.le).continuous.continuousOn
  have hbound : ∀ z : ℂ, ‖z‖ ≤ 16384 → ‖scalarAnchorResponseHol J B hB.le z‖ ≤ A := by
    intro z hz
    exact hA z (by simpa only [mem_closedBall, dist_zero_right] using hz)
  have hApos : 0 < A := zero_lt_one.trans_le
    (thresholdResponse_disk_bound_ge_one _ A (scalarAnchorResponseHol_zero J B hB.le) hbound)
  apply scalarAnchorSquareMass_pos_of_entire _ A B _ hApos.le hB
    (differentiable_scalarAnchorResponseHol J B hB.le)
    (scalarAnchorResponseHol_zero J B hB.le) hbound
    (continuous_scalarAnchorResponsePhysical J B hB.le).continuousOn
  intro t ht
  exact scalarAnchorResponseHol_eq_physical J B hB hunit t ((sqrt_nonneg 2).trans ht.1)

end GapFamily.Analytic
