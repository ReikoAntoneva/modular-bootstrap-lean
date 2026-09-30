import GapFamily.Analytic.Transform.CosRoot
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

noncomputable section
namespace GapFamily.Analytic.CosRootLaplace
open Set MeasureTheory

/-- Principal-power normalization for the Gaussian coefficient in the positive half-plane. -/
theorem gaussian_half_power {z : ℂ} (hz : 0 < z.re) :
    ((Real.pi : ℂ) / z) ^ (1 / 2 : ℂ) =
      (Real.sqrt Real.pi : ℂ) * z ^ (-(1 / 2 : ℂ)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hp0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have harg : z.arg ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff, not_and_or, not_lt]
    exact Or.inl hz.le
  have hp : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    calc
      _ = ((Real.pi ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        simpa using (Complex.ofReal_cpow Real.pi_pos.le (1 / 2 : ℝ)).symm
      _ = _ := by rw [← Real.sqrt_eq_rpow]
  rw [← hp, Complex.cpow_def_of_ne_zero (div_ne_zero hp0 hz0),
    Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hz0,
    ← Complex.exp_add, div_eq_mul_inv,
    Complex.log_ofReal_mul Real.pi_pos (inv_ne_zero hz0), Complex.log_inv z harg,
    Complex.ofReal_log Real.pi_pos.le]
  congr 1
  ring

private theorem gaussian_cos_decomposition (z q : ℂ) (t : ℝ) :
    Complex.exp (-z * (t : ℂ) ^ 2) * Complex.cos (q * (t : ℂ)) =
      (Complex.exp (-z * (t : ℂ) ^ 2 + (Complex.I * q) * (t : ℂ) + 0) +
        Complex.exp (-z * (t : ℂ) ^ 2 + (-Complex.I * q) * (t : ℂ) + 0)) / 2 := by
  rw [Complex.cos, ← mul_div_assoc, mul_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 3 <;> ring

/-- The actual complex cosine Gaussian is ordinarily integrable for every complex frequency. -/
theorem integrable_gaussian_cos {z : ℂ} (hz : 0 < z.re) (q : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ) ^ 2) *
      Complex.cos (q * (t : ℂ))) := by
  have h := ((integrable_cexp_quadratic hz (Complex.I * q) 0).add
    (integrable_cexp_quadratic hz (-Complex.I * q) 0)).div_const (2 : ℂ)
  exact h.congr (Filter.Eventually.of_forall fun t => (gaussian_cos_decomposition z q t).symm)

/-- The literal cosine Gaussian transform with exact principal-power normalization. -/
theorem integral_gaussian_cos {z : ℂ} (hz : 0 < z.re) (q : ℂ) :
    (∫ t : ℝ, Complex.exp (-z * (t : ℂ) ^ 2) * Complex.cos (q * (t : ℂ))) =
      (Real.sqrt Real.pi : ℂ) * z ^ (-(1 / 2 : ℂ)) *
        Complex.exp (-(q ^ 2) / (4 * z)) := by
  simp_rw [gaussian_cos_decomposition]
  rw [integral_div, integral_add (integrable_cexp_quadratic hz (Complex.I * q) 0)
    (integrable_cexp_quadratic hz (-Complex.I * q) 0)]
  rw [integral_cexp_quadratic (by simpa using hz : (-z).re < 0),
    integral_cexp_quadratic (by simpa using hz : (-z).re < 0)]
  have hp : (Complex.I * q) ^ 2 = -(q ^ 2) := by rw [mul_pow, Complex.I_sq]; ring
  have hn : (-Complex.I * q) ^ 2 = -(q ^ 2) := by rw [mul_pow, neg_sq, Complex.I_sq]; ring
  simp only [neg_neg, hp, hn]
  have he : (0 : ℂ) - -(q ^ 2) / (4 * -z) = -(q ^ 2) / (4 * z) := by ring
  rw [he, gaussian_half_power hz]
  ring

/-- Evenness gives the genuine half-line cosine Gaussian integral. -/
theorem integral_gaussian_cos_Ioi {z : ℂ} (hz : 0 < z.re) (q : ℂ) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-z * (t : ℂ) ^ 2) * Complex.cos (q * (t : ℂ))) =
      ((Real.sqrt Real.pi : ℂ) * z ^ (-(1 / 2 : ℂ)) *
        Complex.exp (-(q ^ 2) / (4 * z))) / 2 := by
  let f : ℝ → ℂ := fun t => Complex.exp (-z * (t : ℂ) ^ 2) * Complex.cos (q * (t : ℂ))
  have heven (t : ℝ) : f (-t) = f t := by
    dsimp [f]
    rw [Complex.ofReal_neg, neg_sq, mul_neg, Complex.cos_neg]
  have hleft : (∫ t in Iic 0, f t) = ∫ t in Ioi 0, f t := by
    calc
      _ = ∫ t in Ioi 0, f (-t) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
      _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun t _ => heven t)
  have h := integral_gaussian_cos hz q
  change (∫ t, f t) = _ at h
  rw [← integral_add_compl (s := Ioi 0) measurableSet_Ioi
    (integrable_gaussian_cos hz q), compl_Ioi, hleft] at h
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  simpa only [mul_two] using h

end GapFamily.Analytic.CosRootLaplace
