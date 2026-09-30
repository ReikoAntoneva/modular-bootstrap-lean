import GapFamily.Analytic.Geometry.LaplacianConformalComposition
import GapFamily.Analytic.Geometry.LaplacianHolomorphic
import GapFamily.Analytic.Geometry.LaplacianMobiusAction
import GapFamily.Analytic.Geometry.LaplacianCoordinate

noncomputable section
namespace GapFamily.Analytic.LaplacianCovariance
open UpperHalfPlane
open scoped MatrixGroups ContDiff

/-- A conformal change of coordinates scales the ordinary real Laplacian.
Only the coordinate change is holomorphic; the outer field is arbitrary real C². -/
theorem euclideanLaplacian_comp_complex {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f (g z)) (hg : ContDiffAt ℂ 2 g z) :
    euclideanLaplacian (f ∘ g) z =
      (‖deriv g z‖ ^ 2 : ℝ) • euclideanLaplacian f (g z) := by
  rw [euclideanLaplacian_comp_of_conformal hf (hg.restrict_scalars ℝ)
    (fderiv_real_apply_of_complex (hg.differentiableAt (by norm_num))),
    euclideanLaplacian_eq_zero_of_contDiffAt_complex hg, map_zero, zero_add]

/-- The ordinary negative hyperbolic Laplacian, on an ambient complex representative. -/
def ordinaryHyperbolicLaplacian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (-(z.im ^ 2) : ℝ) • euclideanLaplacian f z

/-- The definition is literally minus height squared times the ordinary two second partials. -/
theorem ordinaryHyperbolicLaplacian_eq_coordinate_deriv {f : ℂ → ℂ} {x y : ℝ}
    (hf : ContDiffAt ℝ 2 f (Complex.mk x y)) :
    ordinaryHyperbolicLaplacian f (Complex.mk x y) =
      (-(y ^ 2) : ℝ) •
        (deriv (deriv (fun a : ℝ => f (Complex.mk a y))) x +
          deriv (deriv (fun b : ℝ => f (Complex.mk x b))) y) := by
  rw [ordinaryHyperbolicLaplacian, euclideanLaplacian_eq_coordinate_deriv hf]

/-- Exact second-order covariance under the actual SL₂(ℝ) action, for an arbitrary
real C² complex-valued field. No invariance or holomorphy of the field is assumed. -/
theorem ordinaryHyperbolicLaplacian_comp_rawRealModularAction
    (γ : SL(2, ℝ)) (τ : UpperHalfPlane) {f : ℂ → ℂ}
    (hf : ContDiffAt ℝ 2 f (γ • τ : UpperHalfPlane)) :
    ordinaryHyperbolicLaplacian (f ∘ rawRealModularAction γ) τ =
      ordinaryHyperbolicLaplacian f (γ • τ : UpperHalfPlane) := by
  have hf' : ContDiffAt ℝ 2 f (rawRealModularAction γ τ) := by
    simpa only [rawRealModularAction_coe] using hf
  rw [ordinaryHyperbolicLaplacian, euclideanLaplacian_comp_complex hf'
    (analyticAt_rawRealModularAction γ τ).contDiffAt,
    rawRealModularAction_coe, smul_smul, neg_mul]
  change -(τ.im ^ 2 * ‖deriv (rawRealModularAction γ) τ‖ ^ 2) •
    euclideanLaplacian f (γ • τ : UpperHalfPlane) = _
  rw [hyperbolic_scale_rawRealModularAction γ τ]
  rfl

/-- Integer modular covariance uses exactly the existing full-group raw action. -/
theorem ordinaryHyperbolicLaplacian_comp_rawModularAction
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) {f : ℂ → ℂ}
    (hf : ContDiffAt ℝ 2 f (γ • τ : UpperHalfPlane)) :
    ordinaryHyperbolicLaplacian (f ∘ rawModularAction γ) τ =
      ordinaryHyperbolicLaplacian f (γ • τ : UpperHalfPlane) := by
  exact ordinaryHyperbolicLaplacian_comp_rawRealModularAction (γ : SL(2, ℝ)) τ hf

/-- The upper-half-plane C² hypothesis is sufficient at every transformed point. -/
theorem ordinaryHyperbolicLaplacian_comp_rawRealModularAction_of_contDiffOn
    (γ : SL(2, ℝ)) (τ : UpperHalfPlane) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 f upperHalfPlaneSet) :
    ordinaryHyperbolicLaplacian (f ∘ rawRealModularAction γ) τ =
      ordinaryHyperbolicLaplacian f (γ • τ : UpperHalfPlane) := by
  apply ordinaryHyperbolicLaplacian_comp_rawRealModularAction
  exact hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds (γ • τ : UpperHalfPlane).im_pos)

end GapFamily.Analytic.LaplacianCovariance
