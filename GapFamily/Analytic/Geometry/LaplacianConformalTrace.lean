import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Ring

noncomputable section

namespace GapFamily.Analytic.LaplacianCovariance

/-- The coordinate trace of an arbitrary real bilinear map scales conformally.
The two mixed terms cancel without any symmetry assumption on the bilinear map. -/
theorem bilinear_conformal_trace
    (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (c : ℂ) :
    B c c + B (c * Complex.I) (c * Complex.I) =
      (‖c‖ ^ 2 : ℝ) • (B 1 1 + B Complex.I Complex.I) := by
  have hz (z : ℂ) : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  have hL (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
      L z = z.re • L 1 + z.im • L Complex.I := by
    conv_lhs => rw [hz z, map_add, map_smul, map_smul]
  have hB (z w : ℂ) : B z w = z.re • B 1 w + z.im • B Complex.I w := by
    conv_lhs => rw [hz z, map_add, map_smul, map_smul]
    rfl
  rw [hB c c, hB (c * Complex.I) (c * Complex.I),
    hL (B 1) c, hL (B Complex.I) c,
    hL (B 1) (c * Complex.I), hL (B Complex.I) (c * Complex.I)]
  apply Complex.ext <;>
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, add_zero] <;> ring

end GapFamily.Analytic.LaplacianCovariance
