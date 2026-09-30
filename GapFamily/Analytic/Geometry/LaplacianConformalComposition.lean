import GapFamily.Analytic.Geometry.LaplacianSecondChain
import GapFamily.Analytic.Geometry.LaplacianConformalTrace

noncomputable section
namespace GapFamily.Analytic.LaplacianCovariance
open scoped ContDiff

/-- The real Hessian chain rule, traced in the actual orthogonal coordinate directions. -/
theorem euclideanLaplacian_comp_of_conformal {f g : ℂ → ℂ} {z c : ℂ}
    (hf : ContDiffAt ℝ 2 f (g z)) (hg : ContDiffAt ℝ 2 g z)
    (hd : ∀ v, fderiv ℝ g z v = c * v) :
    euclideanLaplacian (f ∘ g) z =
      fderiv ℝ f (g z) (euclideanLaplacian g z) +
        (‖c‖ ^ 2 : ℝ) • euclideanLaplacian f (g z) := by
  rw [euclideanLaplacian_eq_hessian_trace (hf.comp z hg),
    second_fderiv_comp hf hg, second_fderiv_comp hf hg,
    hd 1, hd Complex.I, mul_one,
    euclideanLaplacian_eq_hessian_trace hg,
    euclideanLaplacian_eq_hessian_trace hf, map_add]
  have h := bilinear_conformal_trace (fderiv ℝ (fderiv ℝ f) (g z)) c
  linear_combination h

end GapFamily.Analytic.LaplacianCovariance
