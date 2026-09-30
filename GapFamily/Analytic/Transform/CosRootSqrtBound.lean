import GapFamily.Analytic.Transform.CosRoot
import GapFamily.Analytic.Foundation.CoshBound

/-!
# Square-root growth of the entire cosine factor

Comparison with the actual hyperbolic-cosine series gives exponential growth
in the square root of the argument and retains the exact linear zero.
-/

namespace GapFamily.Analytic

/-- Absolute comparison with the hyperbolic-cosine power series. -/
theorem norm_cosRoot_le_cosh_sqrt (z : ℂ) :
    ‖cosRoot z‖ ≤ Real.cosh (Real.sqrt ‖z‖) := by
  apply tsum_of_norm_bounded (Real.hasSum_cosh (Real.sqrt ‖z‖))
  intro n
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  rw [pow_mul, Real.sq_sqrt (norm_nonneg z)]

/-- The entire energy factor grows exponentially in the square root of its argument. -/
theorem norm_cosRoot_le_exp_sqrt (z : ℂ) :
    ‖cosRoot z‖ ≤ Real.exp (Real.sqrt ‖z‖) :=
  (norm_cosRoot_le_cosh_sqrt z).trans (cosh_le_exp (Real.sqrt_nonneg _))

/-- Removing the constant coefficient retains the vanishing at zero. -/
theorem norm_cosRoot_sub_one_le_cosh_sqrt (z : ℂ) :
    ‖cosRoot z - 1‖ ≤ Real.cosh (Real.sqrt ‖z‖) - 1 := by
  have htail : cosRoot z - 1 =
      ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * z ^ (n + 1) / (2 * (n + 1)).factorial := by
    have h := (summable_cosRoot z).sum_add_tsum_nat_add 1
    apply sub_eq_iff_eq_add.mpr
    simpa [cosRoot, add_comm] using h.symm
  have hmajor : HasSum
      (fun n : ℕ => (Real.sqrt ‖z‖) ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ))
      (Real.cosh (Real.sqrt ‖z‖) - 1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr (Real.hasSum_cosh (Real.sqrt ‖z‖))
  rw [htail]
  apply tsum_of_norm_bounded hmajor
  intro n
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  rw [pow_mul, Real.sq_sqrt (norm_nonneg z)]

/-- The remainder has a linear zero with square-root exponential growth. -/
theorem norm_cosRoot_sub_one_le_exp_sqrt (z : ℂ) :
    ‖cosRoot z - 1‖ ≤ ‖z‖ / 2 * Real.exp (Real.sqrt ‖z‖) := by
  calc
    _ ≤ Real.cosh (Real.sqrt ‖z‖) - 1 := norm_cosRoot_sub_one_le_cosh_sqrt z
    _ ≤ (Real.sqrt ‖z‖) ^ 2 / 2 * Real.exp (Real.sqrt ‖z‖) :=
      cosh_sub_one_le (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sq_sqrt (norm_nonneg z)]

/-- The intact product-minus-one has its full linear vanishing factor. -/
theorem norm_cosRoot_mul_sub_one_le_exp_sqrt (z w : ℂ) :
    ‖cosRoot z * cosRoot w - 1‖ ≤
      (‖z‖ + ‖w‖) / 2 * Real.exp (Real.sqrt ‖z‖ + Real.sqrt ‖w‖) := by
  rw [show cosRoot z * cosRoot w - 1 =
    (cosRoot z - 1) * cosRoot w + (cosRoot w - 1) by ring]
  calc
    _ ≤ ‖(cosRoot z - 1) * cosRoot w‖ + ‖cosRoot w - 1‖ := norm_add_le _ _
    _ ≤ (‖z‖ / 2 * Real.exp (Real.sqrt ‖z‖)) * Real.exp (Real.sqrt ‖w‖) +
        ‖w‖ / 2 * Real.exp (Real.sqrt ‖w‖) := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul (norm_cosRoot_sub_one_le_exp_sqrt z)
        (norm_cosRoot_le_exp_sqrt w) (norm_nonneg _) (by positivity))
        (norm_cosRoot_sub_one_le_exp_sqrt w)
    _ = ‖z‖ / 2 * Real.exp (Real.sqrt ‖z‖ + Real.sqrt ‖w‖) +
        ‖w‖ / 2 * Real.exp (Real.sqrt ‖w‖) := by rw [Real.exp_add]; ring
    _ ≤ ‖z‖ / 2 * Real.exp (Real.sqrt ‖z‖ + Real.sqrt ‖w‖) +
        ‖w‖ / 2 * Real.exp (Real.sqrt ‖z‖ + Real.sqrt ‖w‖) := by
      gcongr
      exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Denominator scaling retains quadratic arithmetic decay. -/
theorem norm_cosRoot_mul_sub_one_div_le_exp_sqrt (z w : ℂ) (d : ℝ) (hd : 1 ≤ d) :
    ‖cosRoot (z / d) * cosRoot (w / d) - 1‖ ≤
      ((‖z‖ + ‖w‖) / 2 * Real.exp (Real.sqrt ‖z‖ + Real.sqrt ‖w‖)) / d := by
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have hz : ‖z / (d : ℂ)‖ = ‖z‖ / d := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0]
  have hw : ‖w / (d : ℂ)‖ = ‖w‖ / d := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0]
  calc
    _ ≤ (‖z‖ / d + ‖w‖ / d) / 2 *
        Real.exp (Real.sqrt (‖z‖ / d) + Real.sqrt (‖w‖ / d)) := by
      simpa only [hz, hw] using norm_cosRoot_mul_sub_one_le_exp_sqrt (z / d) (w / d)
    _ ≤ (‖z‖ / d + ‖w‖ / d) / 2 *
        Real.exp (Real.sqrt ‖z‖ + Real.sqrt ‖w‖) := by
      gcongr
      · exact div_le_self (norm_nonneg _) hd
      · exact div_le_self (norm_nonneg _) hd
    _ = _ := by ring

end GapFamily.Analytic
