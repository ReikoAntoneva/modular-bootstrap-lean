import GapFamily.Analytic.Spatial.SpatialPointParameterDeriv

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open Complex
open scoped Topology ContDiff

theorem pointParameter_fderiv_one {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    fderiv ℝ (fun v : ℂ => pointParameter v w) z 1 =
      deriv (fun t : ℝ => pointParameter (Complex.mk t z.im) w) z.re := by
  have hc : HasDerivAt (fun t : ℝ => Complex.mk t z.im) 1 z.re := by
    simpa only [Complex.mk_eq_add_mul_I, Complex.ofRealCLM_apply, Complex.ofReal_one] using
      (Complex.ofRealCLM.hasDerivAt (x := z.re)).add_const ((z.im : ℂ) * Complex.I)
  have hq := (pointParameter_contDiffAt_left hz hw).differentiableAt (by simp)
  have h := hq.hasFDerivAt.comp_hasDerivAt_of_eq z.re hc (by simp)
  exact h.deriv.symm

theorem pointParameter_fderiv_I {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    fderiv ℝ (fun v : ℂ => pointParameter v w) z Complex.I =
      deriv (fun t : ℝ => pointParameter (Complex.mk z.re t) w) z.im := by
  have hc : HasDerivAt (fun t : ℝ => Complex.mk z.re t) Complex.I z.im := by
    simpa only [Complex.mk_eq_add_mul_I, Complex.ofRealCLM_apply, Complex.ofReal_one,
      one_mul] using
      ((Complex.ofRealCLM.hasDerivAt (x := z.im)).mul_const Complex.I).const_add (z.re : ℂ)
  have hq := (pointParameter_contDiffAt_left hz hw).differentiableAt (by simp)
  have h := hq.hasFDerivAt.comp_hasDerivAt_of_eq z.im hc (by simp)
  exact h.deriv.symm

private theorem realCLM_apply_coordinate (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
    L v = v.re * L 1 + v.im * L Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by simp [Complex.real_smul]
  conv_lhs => rw [hv, map_add, map_smul, map_smul]
  rfl

/-- The norm of the actual differential obeys the hyperbolic radial gradient bound. -/
theorem pointParameter_fderiv_norm_le_self {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    z.im * ‖fderiv ℝ (fun v : ℂ => pointParameter v w) z‖ ≤ pointParameter z w := by
  let L := fderiv ℝ (fun v : ℂ => pointParameter v w) z
  let q := pointParameter z w
  have hq : 0 ≤ q := (pointParameter_pos hz hw).le
  have hgrad : (z.im * L 1)^2 + (z.im * L Complex.I)^2 = q * (q - 1) := by
    dsimp only [L, q]
    rw [pointParameter_fderiv_one hz hw, pointParameter_fderiv_I hz hw]
    have h := pointParameter_gradient_sq w z.re z.im hz.ne' hw.ne'
    simpa only [Complex.eta, mul_pow, ← mul_add] using h
  have hop : ‖z.im • L‖ ≤ q := by
    apply ContinuousLinearMap.opNorm_le_bound _ hq
    intro v
    have hc : (z.im * L v)^2 ≤ q^2 * ‖v‖^2 := by
      rw [realCLM_apply_coordinate L v]
      have hv : v.re^2 + v.im^2 = ‖v‖^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        ring
      nlinarith [sq_nonneg ((z.im * L 1) * v.im - (z.im * L Complex.I) * v.re),
        sq_nonneg ‖v‖]
    simpa only [smul_apply, smul_eq_mul, Real.norm_eq_abs,
      ← abs_mul] using (sq_le_sq₀ (abs_nonneg (z.im * L v))
        (mul_nonneg hq (norm_nonneg v))).mp (by simpa [sq_abs, mul_pow] using hc)
  simpa only [norm_smul, Real.norm_of_nonneg hz.le] using hop

/-- A coarser estimate convenient for radial chain-rule constants. -/
theorem pointParameter_fderiv_norm_le {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    z.im * ‖fderiv ℝ (fun v : ℂ => pointParameter v w) z‖ ≤ 2 * pointParameter z w := by
  exact (pointParameter_fderiv_norm_le_self hz hw).trans (by nlinarith [pointParameter_pos hz hw])

end GapFamily.Analytic.SpatialPoint
