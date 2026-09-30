import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import GapFamily.Analytic.Elliptic.WeakLaplacianMollifier

noncomputable section
namespace GapFamily.Analytic.LaplacianCovariance
open Filter
open scoped Topology

/-- The actual real derivative of a complex-differentiable map is complex multiplication. -/
theorem fderiv_real_apply_of_complex {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) (v : ℂ) :
    fderiv ℝ g z v = deriv g z * v := by
  rw [hg.fderiv_restrictScalars (𝕜 := ℝ)]
  exact fderiv_eq_deriv_mul

private theorem real_hessian_directional {g : ℂ → ℂ} {z : ℂ}
    (hg : ContDiffAt ℝ 2 g z) (v w : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ g y v) z w =
      fderiv ℝ (fderiv ℝ g) z w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

/-- Restricting both slots of an actual complex Hessian gives the real Hessian. -/
theorem holomorphic_real_hessian {g : ℂ → ℂ} {z : ℂ}
    (hg : ContDiffAt ℂ 2 g z) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ g) z v w = fderiv ℂ (fderiv ℂ g) z v w := by
  have hd : DifferentiableAt ℂ (fderiv ℂ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdir : DifferentiableAt ℂ (fun y => fderiv ℂ g y w) z :=
    hd.clm_apply (differentiableAt_const w)
  have heq : (fun y => fderiv ℝ g y w) =ᶠ[𝓝 z]
      (fun y => fderiv ℂ g y w) := by
    filter_upwards [hg.eventually (by norm_num)] with y hy
    rw [(hy.differentiableAt (by norm_num)).fderiv_restrictScalars (𝕜 := ℝ)]
    rfl
  rw [← real_hessian_directional (hg.restrict_scalars ℝ) w v, heq.fderiv_eq,
    hdir.fderiv_restrictScalars (𝕜 := ℝ)]
  change fderiv ℂ (fun y => fderiv ℂ g y w) z v = _
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- The real Hessian of a twice complex-differentiable map has zero planar trace. -/
theorem holomorphic_real_hessian_trace_zero {g : ℂ → ℂ} {z : ℂ}
    (hg : ContDiffAt ℂ 2 g z) :
    fderiv ℝ (fderiv ℝ g) z 1 1 +
      fderiv ℝ (fderiv ℝ g) z Complex.I Complex.I = 0 := by
  rw [holomorphic_real_hessian hg, holomorphic_real_hessian hg]
  let B := fderiv ℂ (fderiv ℂ g) z
  change B 1 1 + B Complex.I Complex.I = 0
  have hBI : B Complex.I Complex.I = -B 1 1 := by
    calc
      B Complex.I Complex.I = B (Complex.I • (1 : ℂ)) (Complex.I • (1 : ℂ)) := by simp
      _ = Complex.I • (Complex.I • B 1 1) := by simp only [map_smul, smul_apply]
      _ = -B 1 1 := by
        simp only [smul_eq_mul, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  rw [hBI, add_neg_cancel]

/-- The actual ordinary Euclidean Laplacian vanishes for a C² complex map. -/
theorem euclideanLaplacian_eq_zero_of_contDiffAt_complex {g : ℂ → ℂ} {z : ℂ}
    (hg : ContDiffAt ℂ 2 g z) : euclideanLaplacian g z = 0 := by
  rw [euclideanLaplacian, real_hessian_directional (hg.restrict_scalars ℝ),
    real_hessian_directional (hg.restrict_scalars ℝ)]
  exact holomorphic_real_hessian_trace_zero hg

end GapFamily.Analytic.LaplacianCovariance
