import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.Laplacian
import GapFamily.Analytic.Elliptic.WeakLaplacianMollifier

noncomputable section
namespace GapFamily.Analytic.LaplacianCovariance
open Filter Set InnerProductSpace
open scoped Topology ContDiff

/-- The ordinary second real derivative of a composite, with arbitrary real C² outer function. -/
theorem second_fderiv_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f (g z)) (hg : ContDiffAt ℝ 2 g z) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) z v w =
      fderiv ℝ f (g z) (fderiv ℝ (fderiv ℝ g) z v w) +
        fderiv ℝ (fderiv ℝ f) (g z) (fderiv ℝ g z v) (fderiv ℝ g z w) := by
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) (g z) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg' : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgc : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have heq : fderiv ℝ (f ∘ g) =ᶠ[𝓝 z]
      (fun y => (fderiv ℝ f (g y)).comp (fderiv ℝ g y)) := by
    have hfe := hg.continuousAt.tendsto.eventually (hf.eventually (by norm_num))
    filter_upwards [hfe, hg.eventually (by norm_num)] with y hfy hgy
    exact fderiv_comp y (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  have h := ((hf'.hasFDerivAt.comp z hgc.hasFDerivAt).clm_comp
    hg'.hasFDerivAt).fderiv
  dsimp only [Function.comp_def] at h
  rw [heq.fderiv_eq, h]
  rfl

/-- The nested directional derivative is the corresponding real Hessian entry. -/
theorem second_directional_eq {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (v w : ℂ) :
    fderiv ℝ (fun x => fderiv ℝ f x w) z v = fderiv ℝ (fderiv ℝ f) z v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- The project's ordinary coordinate Laplacian is exactly the trace of the real Hessian. -/
theorem euclideanLaplacian_eq_hessian_trace {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    euclideanLaplacian f z =
      fderiv ℝ (fderiv ℝ f) z 1 1 +
        fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I := by
  rw [euclideanLaplacian, second_directional_eq hf, second_directional_eq hf]

theorem euclideanLaplacian_eq_mathlib {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    euclideanLaplacian f z = Laplacian.laplacian f z := by
  rw [euclideanLaplacian_eq_hessian_trace hf,
    laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

end GapFamily.Analytic.LaplacianCovariance
