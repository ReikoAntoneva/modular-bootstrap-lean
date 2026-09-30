import GapFamily.Analytic.Spatial.SpatialOrbitSummable

/-! Actual nonnegative real orbit values and their exact norm mass for real exponents. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open MeasureTheory UpperHalfPlane
open scoped MatrixGroups

private theorem pointKernel_real_eq_coe_norm (s : ℝ) (z w : UpperHalfPlane) :
    pointKernel (s : ℂ) z w = (‖pointKernel (s : ℂ) z w‖ : ℂ) := by
  rw [norm_pointKernel_real_exponent, pointKernel]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow (pointParameter_pos z.im_pos w.im_pos).le]
  push_cast
  rfl

private theorem pointKernel_real_re_nonneg (s : ℝ) (z w : UpperHalfPlane) :
    0 ≤ (pointKernel (s : ℂ) z w).re := by
  rw [pointKernel_real_eq_coe_norm, Complex.ofReal_re]
  exact norm_nonneg _

private theorem pointKernel_real_im_eq_zero (s : ℝ) (z w : UpperHalfPlane) :
    (pointKernel (s : ℂ) z w).im = 0 := by
  rw [pointKernel_real_eq_coe_norm, Complex.ofReal_im]

theorem spatialOrbitKernel_re_nonneg (s : ℝ) (hs : 1 < s) (z w : UpperHalfPlane) :
    0 ≤ (spatialOrbitKernel (s : ℂ) z w).re := by
  have hsum := summable_spatialOrbit (s : ℂ) (by simpa using hs) z w
  rw [spatialOrbitKernel_eq_half_tsum_right, Complex.mul_re, Complex.re_tsum hsum]
  norm_num
  exact tsum_nonneg (fun γ => pointKernel_real_re_nonneg s z (γ • w))

theorem spatialOrbitKernel_im_eq_zero (s : ℝ) (hs : 1 < s) (z w : UpperHalfPlane) :
    (spatialOrbitKernel (s : ℂ) z w).im = 0 := by
  have hsum := summable_spatialOrbit (s : ℂ) (by simpa using hs) z w
  rw [spatialOrbitKernel_eq_half_tsum_right, Complex.mul_im, Complex.im_tsum hsum]
  simp only [pointKernel_real_im_eq_zero, tsum_zero]
  norm_num

theorem norm_spatialOrbitKernel_eq_re (s : ℝ) (hs : 1 < s) (z w : UpperHalfPlane) :
    ‖spatialOrbitKernel (s : ℂ) z w‖ = (spatialOrbitKernel (s : ℂ) z w).re := by
  have hreal : spatialOrbitKernel (s : ℂ) z w =
      ((spatialOrbitKernel (s : ℂ) z w).re : ℂ) := by
    apply Complex.ext <;> simp [spatialOrbitKernel_im_eq_zero s hs z w]
  conv_lhs => rw [hreal]
  exact Complex.norm_of_nonneg (spatialOrbitKernel_re_nonneg s hs z w)

theorem integrable_norm_spatialOrbitKernel (s : ℝ) (hs : 1 < s) (w : UpperHalfPlane) :
    Integrable (fun z : UpperHalfPlane => ‖spatialOrbitKernel (s : ℂ) z w‖) modularMeasure :=
  (integrable_spatialOrbitKernel (s : ℂ) (by simpa using hs) w).norm

theorem integral_norm_spatialOrbitKernel (s : ℝ) (hs : 1 < s) (w : UpperHalfPlane) :
    (∫ z : UpperHalfPlane, ‖spatialOrbitKernel (s : ℂ) z w‖ ∂modularMeasure) =
      Real.pi / (s - 1) := by
  calc
    _ = ∫ z : UpperHalfPlane, (spatialOrbitKernel (s : ℂ) z w).re ∂modularMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => norm_spatialOrbitKernel_eq_re s hs z w)
    _ = (∫ z : UpperHalfPlane, spatialOrbitKernel (s : ℂ) z w ∂modularMeasure).re :=
      Complex.reCLM.integral_comp_comm
        (integrable_spatialOrbitKernel (s : ℂ) (by simpa using hs) w)
    _ = _ := by rw [integral_spatialOrbitKernel s hs w]; rfl

theorem integrable_norm_spatialOrbitKernel_column (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    Integrable (fun w : UpperHalfPlane => ‖spatialOrbitKernel (s : ℂ) z w‖) modularMeasure := by
  simpa only [spatialOrbitKernel_symm (s : ℂ) z] using
    integrable_norm_spatialOrbitKernel s hs z

theorem integral_norm_spatialOrbitKernel_column (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    (∫ w : UpperHalfPlane, ‖spatialOrbitKernel (s : ℂ) z w‖ ∂modularMeasure) =
      Real.pi / (s - 1) := by
  simpa only [spatialOrbitKernel_symm (s : ℂ) z] using
    integral_norm_spatialOrbitKernel s hs z

end GapFamily.Analytic.SpatialPoint
