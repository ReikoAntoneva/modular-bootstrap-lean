import GapFamily.Analytic.Spatial.SpatialDiskApproximation
import GapFamily.Analytic.Spatial.SpatialCayleyPointIntegral
import GapFamily.Analytic.Spatial.SpatialPointCenterTransport

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory Metric UpperHalfPlane
open scoped Topology BoundedContinuousFunction

/-- The actual normalized whole-hyperbolic-plane kernel converges to evaluation at I
against every bounded continuous complex test function. -/
theorem pointAverage_tendsto_I (f : UpperHalfPlane →ᵇ ℂ) :
    Tendsto (fun s : ℝ => pointAverage s UpperHalfPlane.I f) atTop (𝓝 (f UpperHalfPlane.I)) := by
  let F : ℂ → ℂ := fun ζ => f (cayleyUpper ζ)
  have hF : AEStronglyMeasurable F (volume.restrict (ball 0 1)) :=
    (f.continuous.comp_continuousOn continuousOn_cayleyUpper).aestronglyMeasurable measurableSet_ball
  have hcont : ContinuousAt F 0 := f.continuous.continuousAt.comp continuousAt_cayleyUpper_zero
  have hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ ball (0 : ℂ) 1, ‖F ζ‖ ≤ M :=
    ⟨‖f‖, norm_nonneg f, fun ζ _ => f.norm_coe_le_norm (cayleyUpper ζ)⟩
  have ht := tendsto_normalized_spatialDiskDensity_integral hF hcont hb
  have he (s : ℝ) : pointAverage s UpperHalfPlane.I f =
      ((s - 1) / Real.pi : ℝ) •
        ∫ ζ : ℂ in ball 0 1, (spatialDiskDensity s ζ : ℂ) * F ζ := by
    rw [pointAverage, Complex.real_smul]
    congr 1
    calc
      _ = ∫ w : UpperHalfPlane, pointKernel (s : ℂ) w Complex.I * f w := by
        apply integral_congr_ae
        filter_upwards [] with w
        rw [pointKernel_symm]
        rfl
      _ = _ := integral_pointKernel_test_eq_cayley s f
  have hp : Tendsto (fun s : ℝ => pointAverage s UpperHalfPlane.I f) atTop (𝓝 (F 0)) :=
    ht.congr' (Eventually.of_forall fun s => (he s).symm)
  simpa only [F, cayleyUpper_zero] using hp

/-- The literal mass-normalized point kernel is an approximate identity at every
upper-half-plane center. Integrability for all s>1 is supplied by the actual bounded-test theorem. -/
theorem pointAverage_tendsto (z : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ) :
    Tendsto (fun s : ℝ => pointAverage s z f) atTop (𝓝 (f z)) := by
  have h := pointAverage_tendsto_I (pointPullback z f)
  have he : (fun s : ℝ => pointAverage s UpperHalfPlane.I (pointPullback z f)) =
      (fun s : ℝ => pointAverage s z f) := funext (fun s => (pointAverage_move s z f).symm)
  rw [he, pointPullback_at_I] at h
  exact h

end GapFamily.Analytic.SpatialPoint
