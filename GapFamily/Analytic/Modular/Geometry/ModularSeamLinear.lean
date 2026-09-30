import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Conformal change of a real-linear planar derivative

Multiplication by a complex number rotates and scales the standard real basis.
The sum of the squared image norms under an arbitrary real-linear derivative
scales by the squared complex norm.
-/

noncomputable section

namespace GapFamily.Analytic

/-- The Frobenius energy of a real-linear planar map scales conformally. -/
theorem norm_sq_apply_add_norm_sq_apply_mul_I
    (L : ℂ →L[ℝ] ℂ) (q : ℂ) :
    ‖L q‖ ^ 2 + ‖L (q * Complex.I)‖ ^ 2 =
      ‖q‖ ^ 2 * (‖L 1‖ ^ 2 + ‖L Complex.I‖ ^ 2) := by
  have hL (z : ℂ) : L z = z.re • L 1 + z.im • L Complex.I := by
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
    conv_lhs => rw [hz, map_add, map_smul, map_smul]
  rw [hL q, hL (q * Complex.I)]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, add_zero]
  ring

end GapFamily.Analytic
