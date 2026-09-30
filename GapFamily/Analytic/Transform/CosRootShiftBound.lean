import GapFamily.Analytic.Transform.CosRoot
import GapFamily.Analytic.Transform.ComplexCosStripBound
import Mathlib.Analysis.RCLike.Sqrt

/-!
# Imaginary growth after a nonnegative square shift

The square root is used only pointwise to estimate the entire function `cosRoot`.
No analytic choice of a square root is asserted.
-/

noncomputable section

namespace GapFamily.Analytic

/-- Every square root of `z²+d`, for `d ≥ 0`, has imaginary part no larger
than that of `z`. This is independent of the choice of square root. -/
theorem abs_im_le_of_sq_eq_sq_add (z w : ℂ) (d : ℝ) (hd : 0 ≤ d)
    (hw : w ^ 2 = z ^ 2 + (d : ℂ)) : |w.im| ≤ |z.im| := by
  have hn := norm_add_le (z ^ 2) (d : ℂ)
  rw [← hw, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hd] at hn
  have hr := congrArg Complex.re hw
  simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.ofReal_re] at hr
  have hz := Complex.sq_norm_sub_sq_re z
  have hw' := Complex.sq_norm_sub_sq_re w
  apply (sq_le_sq).mp
  nlinarith

/-- The principal square root obeys the same pointwise strip bound. -/
theorem abs_im_sqrt_sq_add_le (z : ℂ) (d : ℝ) (hd : 0 ≤ d) :
    |(Complex.sqrt (z ^ 2 + (d : ℂ))).im| ≤ |z.im| := by
  apply abs_im_le_of_sq_eq_sq_add z _ d hd
  exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)

private theorem scaled_sqrt_sq (z : ℂ) (k d : ℝ) (hk : 0 ≤ k) :
    ((Real.sqrt k : ℂ) * Complex.sqrt (z ^ 2 + (d : ℂ))) ^ 2 =
      (k : ℂ) * (z ^ 2 + (d : ℂ)) := by
  rw [mul_pow]
  have hk' : (Real.sqrt k : ℂ) ^ 2 = (k : ℂ) := by
    exact_mod_cast Real.sq_sqrt hk
  rw [hk']
  congr 1
  exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)

private theorem scaled_sqrt_im_le (z : ℂ) (k d : ℝ) (hd : 0 ≤ d) :
    |((Real.sqrt k : ℂ) * Complex.sqrt (z ^ 2 + (d : ℂ))).im| ≤
      Real.sqrt k * |z.im| := by
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, abs_mul, abs_of_nonneg (Real.sqrt_nonneg k)]
  exact mul_le_mul_of_nonneg_left (abs_im_sqrt_sq_add_le z d hd) (Real.sqrt_nonneg _)

/-- A nonnegative square shift and scale preserve imaginary-only growth. -/
theorem norm_cosRoot_shift_le (z : ℂ) (k d : ℝ) (hk : 0 ≤ k) (hd : 0 ≤ d) :
    ‖cosRoot ((k : ℂ) * (z ^ 2 + (d : ℂ)))‖ ≤
      Real.exp (Real.sqrt k * |z.im|) := by
  rw [← scaled_sqrt_sq z k d hk, cosRoot_sq]
  exact (norm_complex_cos_le_exp_abs_im _).trans
    (Real.exp_le_exp.mpr (scaled_sqrt_im_le z k d hd))

/-- The shifted remainder retains the linear zero in the scale, with the same
imaginary-only exponential as the original entire cosine. -/
theorem norm_cosRoot_shift_sub_one_le (z : ℂ) (k d : ℝ) (hk : 0 ≤ k) (hd : 0 ≤ d) :
    ‖cosRoot ((k : ℂ) * (z ^ 2 + (d : ℂ))) - 1‖ ≤
      k * (‖z‖ ^ 2 + d) / 2 * Real.exp (Real.sqrt k * |z.im|) := by
  have hnorm : ‖(Real.sqrt k : ℂ) * Complex.sqrt (z ^ 2 + (d : ℂ))‖ ^ 2 ≤
      k * (‖z‖ ^ 2 + d) := by
    rw [← norm_pow, scaled_sqrt_sq z k d hk, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hk]
    apply mul_le_mul_of_nonneg_left _ hk
    have h := norm_add_le (z ^ 2) (d : ℂ)
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd] at h
    exact h
  rw [← scaled_sqrt_sq z k d hk, cosRoot_sq]
  exact (norm_complex_cos_sub_one_le_sq_mul_exp_abs_im _).trans
    (mul_le_mul (div_le_div_of_nonneg_right hnorm (by norm_num))
      (Real.exp_le_exp.mpr (scaled_sqrt_im_le z k d hd))
      (Real.exp_pos _).le (by positivity))

/-- The intact product-minus-one keeps its scale zero on an input strip. -/
theorem norm_cosRoot_shift_mul_sub_one_le (z : ℂ) (k l d D : ℝ)
    (hk : 0 ≤ k) (hl : 0 ≤ l) (hd : 0 ≤ d) (hD : 0 ≤ D) :
    ‖cosRoot ((k : ℂ) * (z ^ 2 + (d : ℂ))) *
      cosRoot ((l : ℂ) * (z ^ 2 + (D : ℂ))) - 1‖ ≤
      (k * (‖z‖ ^ 2 + d) + l * (‖z‖ ^ 2 + D)) / 2 *
        Real.exp ((Real.sqrt k + Real.sqrt l) * |z.im|) := by
  let u := cosRoot ((k : ℂ) * (z ^ 2 + (d : ℂ)))
  let v := cosRoot ((l : ℂ) * (z ^ 2 + (D : ℂ)))
  change ‖u * v - 1‖ ≤ _
  rw [show u * v - 1 = (u - 1) * v + (v - 1) by ring]
  calc
    _ ≤ ‖u - 1‖ * ‖v‖ + ‖v - 1‖ := by
      simpa only [norm_mul] using norm_add_le ((u - 1) * v) (v - 1)
    _ ≤ (k * (‖z‖ ^ 2 + d) / 2 * Real.exp (Real.sqrt k * |z.im|)) *
        Real.exp (Real.sqrt l * |z.im|) +
        l * (‖z‖ ^ 2 + D) / 2 * Real.exp (Real.sqrt l * |z.im|) := by
      exact add_le_add (mul_le_mul (norm_cosRoot_shift_sub_one_le z k d hk hd)
        (norm_cosRoot_shift_le z l D hl hD) (norm_nonneg _) (by positivity))
        (norm_cosRoot_shift_sub_one_le z l D hl hD)
    _ = k * (‖z‖ ^ 2 + d) / 2 * Real.exp ((Real.sqrt k + Real.sqrt l) * |z.im|) +
        l * (‖z‖ ^ 2 + D) / 2 * Real.exp (Real.sqrt l * |z.im|) := by
      rw [add_mul, Real.exp_add]
      ring
    _ ≤ k * (‖z‖ ^ 2 + d) / 2 * Real.exp ((Real.sqrt k + Real.sqrt l) * |z.im|) +
        l * (‖z‖ ^ 2 + D) / 2 * Real.exp ((Real.sqrt k + Real.sqrt l) * |z.im|) := by
      gcongr
      exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Denominator division preserves the strip exponential and its full decay. -/
theorem norm_cosRoot_shift_mul_sub_one_div_le (z : ℂ) (k l d D c : ℝ)
    (hk : 0 ≤ k) (hl : 0 ≤ l) (hd : 0 ≤ d) (hD : 0 ≤ D) (hc : 1 ≤ c) :
    ‖cosRoot (((k : ℂ) * (z ^ 2 + (d : ℂ))) / (c : ℂ)) *
      cosRoot (((l : ℂ) * (z ^ 2 + (D : ℂ))) / (c : ℂ)) - 1‖ ≤
      ((k * (‖z‖ ^ 2 + d) + l * (‖z‖ ^ 2 + D)) / 2 *
        Real.exp ((Real.sqrt k + Real.sqrt l) * |z.im|)) / c := by
  have hc0 : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hc
  have h := norm_cosRoot_shift_mul_sub_one_le z (k / c) (l / c) d D
    (div_nonneg hk hc0) (div_nonneg hl hc0) hd hD
  have heq (a b : ℝ) : ((a / c : ℝ) : ℂ) * (z ^ 2 + (b : ℂ)) =
      ((a : ℂ) * (z ^ 2 + (b : ℂ))) / (c : ℂ) := by push_cast; ring
  rw [heq k d, heq l D] at h
  refine h.trans ?_
  calc
    _ ≤ (k / c * (‖z‖ ^ 2 + d) + l / c * (‖z‖ ^ 2 + D)) / 2 *
        Real.exp ((Real.sqrt k + Real.sqrt l) * |z.im|) := by
      gcongr
      · exact div_le_self hk hc
      · exact div_le_self hl hc
    _ = _ := by ring

end GapFamily.Analytic
