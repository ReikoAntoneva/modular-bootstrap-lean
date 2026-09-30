import GapFamily.Analytic.Spatial.SpatialRadialPower

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open scoped ContDiff

/-- Exact radial logarithmic derivative norm, including the genuine quarter normalization. -/
theorem radialPower_deriv_norm_mul (s : ℂ) {q : ℝ} (hq : 0 < q) :
    q * ‖deriv (radialPower s) q‖ = ‖s‖ * ‖radialPower s q‖ := by
  rw [deriv_radialPower s hq]
  simp only [radialPower, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.sub_re, Complex.neg_re, Complex.one_re]
  rw [Real.rpow_sub hq, Real.rpow_one]
  field_simp

/-- The literal radial derivative exists at every positive geometric parameter. -/
theorem hasDerivAt_radialPower (s : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (radialPower s) (deriv (radialPower s) q) q :=
  ((radialPower_contDiffAt s hq).differentiableAt (by simp)).hasDerivAt

end GapFamily.Analytic.SpatialPoint
