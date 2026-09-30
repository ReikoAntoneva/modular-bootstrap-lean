import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Complex cosine bound on a horizontal strip

The exponential factor depends only on the imaginary part. The remainder
estimate retains the quadratic zero at the origin.
-/

namespace GapFamily.Analytic

/-- The cosine grows only in the imaginary direction. -/
theorem norm_complex_cos_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos, norm_div, Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖ ≤
        ‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖ := norm_add_le _ _
    _ = Real.exp (-z.im) + Real.exp z.im := by simp [Complex.norm_exp]
    _ ≤ Real.exp |z.im| + Real.exp |z.im| := by
      exact add_le_add (Real.exp_le_exp.mpr (neg_le_abs _))
        (Real.exp_le_exp.mpr (le_abs_self _))
    _ = Real.exp |z.im| * 2 := by ring

/-- The sine estimate also retains its zero at the origin. -/
theorem norm_complex_sin_le_mul_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ ‖z‖ * Real.exp |z.im| := by
  have hder (t : ℝ) : HasDerivAt (fun s : ℝ => Complex.sin ((s : ℂ) * z))
      (Complex.cos ((t : ℂ) * z) * z) t := by
    simpa using ((Complex.hasDerivAt_sin ((t : ℂ) * z)).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).mul_const z)).comp_ofReal
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hder t).hasDerivWithinAt) (C := ‖z‖ * Real.exp |z.im|)
    (by
      intro t ht
      rw [norm_mul]
      have him : |((t : ℂ) * z).im| ≤ |z.im| := by
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          abs_mul, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (abs_nonneg _) ht.2.le
      calc
        ‖Complex.cos ((t : ℂ) * z)‖ * ‖z‖ ≤
            Real.exp |((t : ℂ) * z).im| * ‖z‖ :=
          mul_le_mul_of_nonneg_right (norm_complex_cos_le_exp_abs_im _) (norm_nonneg _)
        _ ≤ Real.exp |z.im| * ‖z‖ := by gcongr
        _ = _ := mul_comm _ _)
  simpa using h

/-- The cosine remainder has a quadratic zero with strip growth. -/
theorem norm_complex_cos_sub_one_le_sq_mul_exp_abs_im (z : ℂ) :
    ‖Complex.cos z - 1‖ ≤ ‖z‖ ^ 2 / 2 * Real.exp |z.im| := by
  have hsin := norm_complex_sin_le_mul_exp_abs_im (z / 2)
  have hsquare := pow_le_pow_left₀ (norm_nonneg (Complex.sin (z / 2))) hsin 2
  have him : |(z / 2).im| = |z.im| / 2 := by simp [abs_div]
  have hexp : Real.exp (|z.im| / 2) ^ 2 = Real.exp |z.im| := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hcos : Complex.cos z - 1 = -2 * Complex.sin (z / 2) ^ 2 := by
    have h := Complex.cos_two_mul_eq_one_sub (x := z / 2)
    rw [show (2 : ℂ) * (z / 2) = z by ring] at h
    rw [h]
    ring
  rw [hcos, norm_mul, norm_pow]
  simp only [norm_neg, Complex.norm_ofNat]
  rw [norm_div, Complex.norm_ofNat, him, mul_pow, hexp] at hsquare
  nlinarith

end GapFamily.Analytic
