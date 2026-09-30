import GapFamily.Analytic.Spatial.SpatialPointKernelBasic
import GapFamily.Analytic.Geometry.LaplacianMobiusCovariance
import GapFamily.Analytic.Elliptic.RealSecondChain

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter
open scoped Topology ContDiff

theorem hasDerivAt_pointParameter_horizontal (w : ℂ) (x y : ℝ)
    (hy : y ≠ 0) (hw : w.im ≠ 0) :
    HasDerivAt (fun t : ℝ => pointParameter (Complex.mk t y) w)
      ((x - w.re) / (2 * y * w.im)) x := by
  have h := (((((hasDerivAt_id x).sub_const w.re).pow 2).add_const
    ((y - w.im) ^ 2)).div_const (4 * y * w.im)).const_add 1
  convert h using 1
  · funext t
    simp only [pointParameter, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Pi.pow_apply, id_eq, pow_two]
  · simp only [id_eq]
    field_simp
    ring

theorem hasDerivAt_pointParameter_vertical (w : ℂ) (x y : ℝ)
    (hy : y ≠ 0) (hw : w.im ≠ 0) :
    HasDerivAt (fun t : ℝ => pointParameter (Complex.mk x t) w)
      ((y ^ 2 - (x - w.re) ^ 2 - w.im ^ 2) / (4 * y ^ 2 * w.im)) y := by
  have hnum := ((((hasDerivAt_id y).sub_const w.im).pow 2).const_add ((x - w.re) ^ 2))
  have hden := ((hasDerivAt_id y).const_mul 4).mul_const w.im
  have h := (hnum.div hden (mul_ne_zero (mul_ne_zero (by norm_num) hy) hw)).const_add 1
  convert h using 1
  · funext t
    simp only [pointParameter, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Pi.pow_apply, Pi.div_apply, id_eq, pow_two]
  · simp only [Pi.pow_apply, id_eq]
    field_simp
    ring

theorem pointParameter_deriv_horizontal (w : ℂ) (x y : ℝ)
    (hy : y ≠ 0) (hw : w.im ≠ 0) :
    deriv (fun t : ℝ => pointParameter (Complex.mk t y) w) x =
      (x - w.re) / (2 * y * w.im) :=
  (hasDerivAt_pointParameter_horizontal w x y hy hw).deriv

theorem pointParameter_deriv_vertical (w : ℂ) (x y : ℝ)
    (hy : y ≠ 0) (hw : w.im ≠ 0) :
    deriv (fun t : ℝ => pointParameter (Complex.mk x t) w) y =
      (y ^ 2 - (x - w.re) ^ 2 - w.im ^ 2) / (4 * y ^ 2 * w.im) :=
  (hasDerivAt_pointParameter_vertical w x y hy hw).deriv

theorem pointParameter_deriv_deriv_horizontal (w : ℂ) (x y : ℝ)
    (hy : y ≠ 0) (hw : w.im ≠ 0) :
    deriv (deriv (fun t : ℝ => pointParameter (Complex.mk t y) w)) x =
      1 / (2 * y * w.im) := by
  have heq : deriv (fun t : ℝ => pointParameter (Complex.mk t y) w) =
      (fun t => (t - w.re) / (2 * y * w.im)) := by
    funext t
    exact pointParameter_deriv_horizontal w t y hy hw
  rw [heq]
  exact (((hasDerivAt_id x).sub_const w.re).div_const (2 * y * w.im)).deriv

theorem pointParameter_deriv_deriv_vertical (w : ℂ) (x y : ℝ)
    (hy : y ≠ 0) (hw : w.im ≠ 0) :
    deriv (deriv (fun t : ℝ => pointParameter (Complex.mk x t) w)) y =
      ((x - w.re) ^ 2 + w.im ^ 2) / (2 * y ^ 3 * w.im) := by
  have heq : deriv (fun t : ℝ => pointParameter (Complex.mk x t) w) =ᶠ[𝓝 y]
      (fun t => (t ^ 2 - (x - w.re) ^ 2 - w.im ^ 2) / (4 * t ^ 2 * w.im)) := by
    filter_upwards [eventually_ne_nhds hy] with t ht
    exact pointParameter_deriv_vertical w x t ht hw
  rw [heq.deriv_eq]
  have hnum := ((((hasDerivAt_id y).pow 2).sub_const ((x - w.re) ^ 2)).sub_const (w.im ^ 2))
  have hden := (((hasDerivAt_id y).pow 2).const_mul 4).mul_const w.im
  have hd := (hnum.div hden (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) hw)).deriv
  simp only [Pi.pow_apply, id_eq] at hd
  change deriv (fun t : ℝ => (t ^ 2 - (x - w.re) ^ 2 - w.im ^ 2) /
    (4 * t ^ 2 * w.im)) y = _ at hd
  rw [hd]
  field_simp
  ring

theorem pointParameter_gradient_sq (w : ℂ) (x y : ℝ)
    (hy : y ≠ 0) (hw : w.im ≠ 0) :
    y ^ 2 * ((deriv (fun t : ℝ => pointParameter (Complex.mk t y) w) x) ^ 2 +
      (deriv (fun t : ℝ => pointParameter (Complex.mk x t) w) y) ^ 2) =
      pointParameter (Complex.mk x y) w * (pointParameter (Complex.mk x y) w - 1) := by
  rw [pointParameter_deriv_horizontal w x y hy hw, pointParameter_deriv_vertical w x y hy hw]
  simp only [pointParameter, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two]
  field_simp
  ring

theorem pointParameter_laplacian_coeff (w : ℂ) (x y : ℝ)
    (hy : y ≠ 0) (hw : w.im ≠ 0) :
    y ^ 2 * (deriv (deriv (fun t : ℝ => pointParameter (Complex.mk t y) w)) x +
      deriv (deriv (fun t : ℝ => pointParameter (Complex.mk x t) w)) y) =
      2 * pointParameter (Complex.mk x y) w - 1 := by
  rw [pointParameter_deriv_deriv_horizontal w x y hy hw,
    pointParameter_deriv_deriv_vertical w x y hy hw]
  simp only [pointParameter, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two]
  field_simp
  ring

/-- The actual ordinary hyperbolic Laplacian of a real radial profile, with
only pointwise real C² regularity of the profile at the geometric parameter. -/
theorem ordinaryHyperbolicLaplacian_comp_pointParameter {g : ℝ → ℂ} {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im)
    (hg : ContDiffAt ℝ 2 g (pointParameter z w)) :
    LaplacianCovariance.ordinaryHyperbolicLaplacian
      (fun v : ℂ => g (pointParameter v w)) z =
      -(pointParameter z w * (pointParameter z w - 1) : ℝ) •
        deriv (deriv g) (pointParameter z w) -
      (2 * pointParameter z w - 1 : ℝ) • deriv g (pointParameter z w) := by
  rcases z with ⟨x, y⟩
  have hq : ContDiffAt ℝ 2 (fun v : ℂ => pointParameter v w) (Complex.mk x y) :=
    (pointParameter_contDiffAt_left hz hw).of_le (by norm_num)
  have hcx : ContDiffAt ℝ 2 (fun t : ℝ => Complex.mk t y) x := by
    simp only [Complex.mk_eq_add_mul_I]
    exact Complex.ofRealCLM.contDiff.contDiffAt.add contDiffAt_const
  have hcy : ContDiffAt ℝ 2 (fun t : ℝ => Complex.mk x t) y := by
    simp only [Complex.mk_eq_add_mul_I]
    exact contDiffAt_const.add (Complex.ofRealCLM.contDiff.contDiffAt.mul contDiffAt_const)
  have hqx := hq.comp x hcx
  have hqy := hq.comp y hcy
  have hf := hg.comp (Complex.mk x y) hq
  simp only [Function.comp_def] at hqx hqy hf
  rw [LaplacianCovariance.ordinaryHyperbolicLaplacian_eq_coordinate_deriv hf,
    deriv_deriv_comp_real hqx hg, deriv_deriv_comp_real hqy hg]
  have hgrad := congrArg Complex.ofReal (pointParameter_gradient_sq w x y hz.ne' hw.ne')
  have hlap := congrArg Complex.ofReal (pointParameter_laplacian_coeff w x y hz.ne' hw.ne')
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat] at hgrad hlap
  simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  linear_combination -(deriv (deriv g) (pointParameter (Complex.mk x y) w)) * hgrad -
    (deriv g (pointParameter (Complex.mk x y) w)) * hlap

end GapFamily.Analytic.SpatialPoint
