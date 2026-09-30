import GapFamily.Analytic.Spatial.SpatialPointLaplace

/-! Branch-controlled complex powers of the two reflected point Laplace rates.
The positive-height half-plane makes their logarithmic arguments cancel. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open Set
open scoped ComplexConjugate

theorem pointLaplaceRate_ne_zero {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    pointLaplaceRate z w ≠ 0 := by
  intro h
  have hh := pointLaplaceRate_re_pos hz hw
  simp [h] at hh

/-- The reflected rates have opposite principal arguments. -/
theorem pointLaplaceRate_arg_add_reflected {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    (pointLaplaceRate z w).arg + (pointLaplaceRate w z).arg = 0 := by
  have harg : (pointLaplaceRate z w).arg ≠ Real.pi := by
    intro h
    have hneg := (Complex.arg_eq_pi_iff.mp h).1
    linarith [pointLaplaceRate_re_pos hz hw]
  rw [pointLaplaceRate_conj z w, Complex.arg_conj, ite_eq_right harg]
  ring

/-- Complex powers multiply without a branch correction for the two rates. -/
theorem pointLaplaceRate_cpow_mul_reflected (s : ℂ) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    (pointLaplaceRate z w) ^ s * (pointLaplaceRate w z) ^ s =
      (pointLaplaceRate z w * pointLaplaceRate w z) ^ s := by
  have hr := pointLaplaceRate_ne_zero hz hw
  have hr' := pointLaplaceRate_ne_zero hw hz
  have hlog : Complex.log (pointLaplaceRate z w * pointLaplaceRate w z) =
      Complex.log (pointLaplaceRate z w) + Complex.log (pointLaplaceRate w z) := by
    apply Complex.log_mul hr hr'
    rw [pointLaplaceRate_arg_add_reflected hz hw]
    exact ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
  rw [Complex.cpow_def_of_ne_zero hr, Complex.cpow_def_of_ne_zero hr',
    Complex.cpow_def_of_ne_zero (mul_ne_zero hr hr'), hlog, add_mul, Complex.exp_add]

/-- The scalar geometric numerator after combining the two rates. -/
def pointGammaLaplaceScale (z w : ℂ) : ℝ := 16 * Real.pi ^ 2 * z.im * w.im

theorem pointGammaLaplaceScale_pos {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    0 < pointGammaLaplaceScale z w := by
  unfold pointGammaLaplaceScale
  positivity

theorem pointLaplaceRate_mul_reflected {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    pointLaplaceRate z w * pointLaplaceRate w z =
      ((pointGammaLaplaceScale z w * pointParameter z w : ℝ) : ℂ) := by
  rw [pointLaplaceRate_conj z w, Complex.mul_conj']
  rw [pointParameter_eq_normSq_sub_conj hz hw]
  have hreal : pointGammaLaplaceScale z w *
      (Complex.normSq (z - conj w) / (4 * z.im * w.im)) =
      ‖pointLaplaceRate z w‖ ^ 2 := by
    rw [pointGammaLaplaceScale, pointLaplaceRate_norm_sq]
    field_simp
    ring
  rw [hreal]
  push_cast
  rfl

/-- Exact point-kernel normalization before inserting the two ordinary Gamma integrals. -/
theorem pointKernel_mul_laplaceRate_powers (s : ℂ) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel s z w * (pointLaplaceRate z w) ^ s * (pointLaplaceRate w z) ^ s =
      (1 / 4 : ℂ) * (pointGammaLaplaceScale z w : ℂ) ^ s := by
  rw [mul_assoc, pointLaplaceRate_cpow_mul_reflected s hz hw,
    pointLaplaceRate_mul_reflected hz hw, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (pointGammaLaplaceScale_pos hz hw).le
      (pointParameter_pos hz hw).le]
  have hp : (pointParameter z w : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pointParameter_pos hz hw).ne'
  have hcancel : (pointParameter z w : ℂ) ^ (-s) * (pointParameter z w : ℂ) ^ s = 1 := by
    rw [← Complex.cpow_add _ _ hp, neg_add_cancel, Complex.cpow_zero]
  unfold pointKernel
  calc
    (1 / 4 : ℂ) * (pointParameter z w : ℂ) ^ (-s) *
        ((pointGammaLaplaceScale z w : ℂ) ^ s * (pointParameter z w : ℂ) ^ s) =
      (1 / 4 : ℂ) * (pointGammaLaplaceScale z w : ℂ) ^ s *
        ((pointParameter z w : ℂ) ^ (-s) * (pointParameter z w : ℂ) ^ s) := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- The Gamma-normalized algebraic factorization for positive-real-part parameters. -/
theorem pointKernel_eq_gamma_rate_product {s z w : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel s z w =
      (1 / 4 : ℂ) * (pointGammaLaplaceScale z w : ℂ) ^ s / Complex.Gamma s ^ 2 *
        (Complex.Gamma s / (pointLaplaceRate z w) ^ s) *
        (Complex.Gamma s / (pointLaplaceRate w z) ^ s) := by
  have hr : (pointLaplaceRate z w) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (pointLaplaceRate_ne_zero hz hw))
  have hr' : (pointLaplaceRate w z) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (pointLaplaceRate_ne_zero hw hz))
  have hgamma := Complex.Gamma_ne_zero_of_re_pos hs
  calc
    pointKernel s z w = ((1 / 4 : ℂ) * (pointGammaLaplaceScale z w : ℂ) ^ s) /
        ((pointLaplaceRate z w) ^ s * (pointLaplaceRate w z) ^ s) := by
      apply (eq_div_iff (mul_ne_zero hr hr')).mpr
      simpa only [mul_assoc] using pointKernel_mul_laplaceRate_powers s hz hw
    _ = _ := by field_simp

end GapFamily.Analytic.SpatialPoint
