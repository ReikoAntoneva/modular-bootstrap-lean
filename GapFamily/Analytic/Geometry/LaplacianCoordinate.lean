import GapFamily.Analytic.Elliptic.WeakLaplacianMollifier

noncomputable section

namespace GapFamily.Analytic

open Filter
open scoped Topology ContDiff

theorem hasDerivAt_horizontalCoordinate (a y : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.mk x y) (1 : ℂ) a := by
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one,
    Complex.mk_eq_add_mul_I] using
    (Complex.ofRealCLM.hasDerivAt (x := a)).add_const ((y : ℂ) * Complex.I)

theorem hasDerivAt_verticalCoordinate (x b : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.mk x y) Complex.I b := by
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul,
    Complex.mk_eq_add_mul_I] using
    ((Complex.ofRealCLM.hasDerivAt (x := b)).mul_const Complex.I).const_add (x : ℂ)

/-- Along a real curve with constant velocity, the second ordinary derivative
is the actual second directional derivative. Only real C² regularity is used. -/
theorem second_deriv_comp_constant_velocity {f : ℂ → ℂ} {c : ℝ → ℂ}
    {x : ℝ} {v : ℂ} (hf : ContDiffAt ℝ 2 f (c x))
    (hc : ∀ a : ℝ, HasDerivAt c v a) :
    deriv (deriv (fun a : ℝ => f (c a))) x =
      fderiv ℝ (fun z => fderiv ℝ f z v) (c x) v := by
  have hfield : DifferentiableAt ℝ (fun z => fderiv ℝ f z v) (c x) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hlocal : ∀ᶠ a in 𝓝 x, ContDiffAt ℝ 2 f (c a) :=
    (hc x).continuousAt.tendsto.eventually (hf.eventually (by norm_num))
  have heq : deriv (fun a : ℝ => f (c a)) =ᶠ[𝓝 x]
      (fun a => fderiv ℝ f (c a) v) := by
    filter_upwards [hlocal] with a ha
    exact ((ha.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt a (hc a)).deriv
  rw [heq.deriv_eq]
  exact (hfield.hasFDerivAt.comp_hasDerivAt x (hc x)).deriv

/-- The existing real Fréchet Laplacian is the literal sum of ordinary second
horizontal and vertical derivatives; no complex differentiability is assumed. -/
theorem euclideanLaplacian_eq_coordinate_deriv {f : ℂ → ℂ} {x y : ℝ}
    (hf : ContDiffAt ℝ 2 f (Complex.mk x y)) :
    euclideanLaplacian f (Complex.mk x y) =
      deriv (deriv (fun a : ℝ => f (Complex.mk a y))) x +
        deriv (deriv (fun b : ℝ => f (Complex.mk x b))) y := by
  have hx := second_deriv_comp_constant_velocity (c := fun a : ℝ => Complex.mk a y)
    hf (fun a => hasDerivAt_horizontalCoordinate a y)
  have hy := second_deriv_comp_constant_velocity (c := fun b : ℝ => Complex.mk x b)
    hf (fun b => hasDerivAt_verticalCoordinate x b)
  rw [euclideanLaplacian, ← hx, ← hy]

end GapFamily.Analytic
