import GapFamily.Analytic.Spatial.SpatialRadialFirstBound
import GapFamily.Analytic.Spatial.SpatialPointParameterFrame

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open scoped ContDiff

/-- Actual spatial Frechet derivative of the literal point kernel. -/
theorem pointKernel_fderiv_left (s : ℂ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    fderiv ℝ (fun v : ℂ => pointKernel s v w) z =
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv (radialPower s) (pointParameter z w))).comp
        (fderiv ℝ (fun v : ℂ => pointParameter v w) z) := by
  have hq := ((pointParameter_contDiffAt_left hz hw).differentiableAt (by simp)).hasFDerivAt
  exact ((hasDerivAt_radialPower s (pointParameter_pos hz hw)).hasFDerivAt.comp z hq).fderiv

/-- Hyperbolic frame operator-norm control, uniform in both upper points. -/
theorem pointKernel_frame_fderiv_norm_le_sharp (s : ℂ) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    z.im * ‖fderiv ℝ (fun v : ℂ => pointKernel s v w) z‖ ≤
      ‖s‖ * ‖pointKernel s z w‖ := by
  rw [pointKernel_fderiv_left s hz hw]
  have hn := ContinuousLinearMap.opNorm_comp_le
    (ContinuousLinearMap.toSpanSingleton ℝ (deriv (radialPower s) (pointParameter z w)))
    (fderiv ℝ (fun v : ℂ => pointParameter v w) z)
  rw [ContinuousLinearMap.norm_toSpanSingleton] at hn
  calc
    _ ≤ z.im * (‖deriv (radialPower s) (pointParameter z w)‖ *
        ‖fderiv ℝ (fun v : ℂ => pointParameter v w) z‖) := mul_le_mul_of_nonneg_left hn hz.le
    _ = (z.im * ‖fderiv ℝ (fun v : ℂ => pointParameter v w) z‖) *
        ‖deriv (radialPower s) (pointParameter z w)‖ := by ring
    _ ≤ pointParameter z w * ‖deriv (radialPower s) (pointParameter z w)‖ :=
      mul_le_mul_of_nonneg_right (pointParameter_fderiv_norm_le_self hz hw) (norm_nonneg _)
    _ = ‖s‖ * ‖pointKernel s z w‖ := radialPower_deriv_norm_mul s (pointParameter_pos hz hw)

/-- A coarse bound useful directly in summable local orbit majorants. -/
theorem pointKernel_frame_fderiv_norm_le (s : ℂ) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    z.im * ‖fderiv ℝ (fun v : ℂ => pointKernel s v w) z‖ ≤
      2 * ‖s‖ * ‖pointKernel s z w‖ := by
  have h := pointKernel_frame_fderiv_norm_le_sharp s hz hw
  nlinarith [mul_nonneg (norm_nonneg s) (norm_nonneg (pointKernel s z w))]

/-- Every fixed frame direction is controlled by the same genuine point kernel. -/
theorem pointKernel_frame_fderiv_apply_norm_le (s : ℂ) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) (v : ℂ) :
    z.im * ‖fderiv ℝ (fun u : ℂ => pointKernel s u w) z v‖ ≤
      2 * ‖s‖ * ‖pointKernel s z w‖ * ‖v‖ := by
  calc
    _ ≤ z.im * (‖fderiv ℝ (fun u : ℂ => pointKernel s u w) z‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ (fun u : ℂ => pointKernel s u w) z).le_opNorm v) hz.le
    _ = (z.im * ‖fderiv ℝ (fun u : ℂ => pointKernel s u w) z‖) * ‖v‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pointKernel_frame_fderiv_norm_le s hz hw) (norm_nonneg v)

end GapFamily.Analytic.SpatialPoint
