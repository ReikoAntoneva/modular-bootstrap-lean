import GapFamily.Analytic.Spatial.SpatialOrbitBoundedBridge
import GapFamily.Analytic.Spatial.SpatialPointApproximation

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane
open scoped BoundedContinuousFunction

/-- The exact mass normalization makes every actual real orbit operator a contraction. -/
theorem norm_normalizedOrbitOperator_le_one (s : ℝ) (hs : 1 < s) :
    ‖normalizedOrbitOperator s hs‖ ≤ 1 := by
  have hc : 0 < (s - 1) / Real.pi := div_pos (sub_pos.mpr hs) Real.pi_pos
  rw [normalizedOrbitOperator, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  calc
    _ ≤ ((s - 1) / Real.pi) * (Real.pi / (s - 1)) :=
      mul_le_mul_of_nonneg_left (norm_spatialOrbitIntegralOperator_le s hs) hc.le
    _ = 1 := by field_simp [Real.pi_ne_zero, (sub_pos.mpr hs).ne']

/-- The actual normalized whole-plane average has the uniform bounded-test estimate. -/
theorem norm_pointAverage_le (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane)
    (f : UpperHalfPlane →ᵇ ℂ) : ‖pointAverage s z f‖ ≤ ‖f‖ := by
  have hc : 0 < (s - 1) / Real.pi := div_pos (sub_pos.mpr hs) Real.pi_pos
  have hi := (integrable_pointKernel_right s hs z).norm.mul_const ‖f‖
  have hb : ‖∫ w : UpperHalfPlane, pointKernel (s : ℂ) z w * f w ∂volume‖ ≤
      (Real.pi / (s - 1)) * ‖f‖ := by
    calc
      _ ≤ ∫ w : UpperHalfPlane, ‖pointKernel (s : ℂ) z w‖ * ‖f‖ ∂volume := by
        apply norm_integral_le_of_norm_le hi
        exact Filter.Eventually.of_forall fun w => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm w) (norm_nonneg _)
      _ = _ := by rw [integral_mul_const, integral_norm_pointKernel s hs z]
  rw [pointAverage, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  calc
    _ ≤ ((s - 1) / Real.pi) * ((Real.pi / (s - 1)) * ‖f‖) :=
      mul_le_mul_of_nonneg_left hb hc.le
    _ = ‖f‖ := by field_simp [Real.pi_ne_zero, (sub_pos.mpr hs).ne']

end GapFamily.Analytic.SpatialPoint
