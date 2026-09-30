import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A linear nonnegative-energy bound for the literal threshold Fourier correction. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory PoincareFourierUnfold

private theorem norm_exp_neg_real_sub_one_le {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp (-(x : ℂ)) - 1‖ ≤ x := by
  have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  have ht := Real.add_one_le_exp (-x)
  have heq : Complex.exp (-(x : ℂ)) - 1 = ((Real.exp (-x) - 1 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_one]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr he)]
  linarith

/-- Positive real energy supplies an extra transformed-height factor with no exponential loss. -/
theorem norm_energyFourierKernel_half_le {c y E : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hE : 0 ≤ E) (j J : ℤ) (t : ℝ) :
    ‖energyFourierKernel c y (E : ℂ) j J (1 / 2 : ℂ) t‖ ≤
      (2 * Real.pi * E) * (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ (3 / 2 : ℝ) := by
  let p : ℝ := y / (c ^ 2 * (t ^ 2 + y ^ 2))
  have hp : 0 < p := by dsimp [p]; positivity
  have he : -2 * (Real.pi : ℂ) * (E : ℂ) * (p : ℂ) =
      -((2 * Real.pi * E * p : ℝ) : ℂ) := by push_cast; ring
  have hphase : ‖Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (p : ℂ)) - 1‖ ≤
      2 * Real.pi * E * p := by
    rw [he]
    exact norm_exp_neg_real_sub_one_le (by positivity)
  rw [energyFourierKernel, norm_mul, norm_fourierKernel hc hy]
  rw [show (1 / 2 : ℂ).re = (1 / 2 : ℝ) by norm_num]
  change p ^ (1 / 2 : ℝ) *
    ‖Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (p : ℂ)) - 1‖ ≤ _
  calc
    _ ≤ p ^ (1 / 2 : ℝ) * (2 * Real.pi * E * p) :=
      mul_le_mul_of_nonneg_left hphase (Real.rpow_nonneg hp.le _)
    _ = _ := by
      change _ = (2 * Real.pi * E) * p ^ (3 / 2 : ℝ)
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add_one hp.ne']
      ring

/-- The actual threshold energy correction is ordinarily integrable for every pair of spins. -/
theorem integrable_energyFourierKernel_half {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    Integrable (energyFourierKernel c y (E : ℂ) j J (1 / 2 : ℂ)) volume :=
  integrable_energyFourierKernel hc hy (E : ℂ) j J (by norm_num)

theorem height_three_halves_le_cauchy {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (t : ℝ) :
    (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ (3 / 2 : ℝ) ≤
      (1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * (1 + (t / y) ^ 2)⁻¹ := by
  have hq : t ^ 2 + y ^ 2 ≠ 0 := by positivity
  have he : y / (c ^ 2 * (t ^ 2 + y ^ 2)) =
      (1 / (c ^ 2 * y)) / (1 + (t / y) ^ 2) := by
    field_simp [hc.ne', hy.ne', hq]
    ring
  have hf : (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ (3 / 2 : ℝ) =
      (1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * (1 + (t / y) ^ 2) ^ (-(3 / 2 : ℝ)) := by
    rw [he, Real.div_rpow (by positivity) (by positivity),
      Real.rpow_neg (by positivity), div_eq_mul_inv]
  rw [hf]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (t / y)]) (by norm_num)

theorem height_three_halves_scale {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    (1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * y = 1 / (c ^ 3 * Real.sqrt y) := by
  have hq : (1 : ℝ) / (c ^ 2 * y) ≠ 0 := by positivity
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add_one hq,
    ← Real.sqrt_eq_rpow]
  simp only [one_div, Real.sqrt_inv, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  field_simp [hc.ne', hy.ne', (Real.sqrt_pos.mpr hy).ne']

/-- The ordinary integrated norm is linear in nonnegative energy, uniform in both spins,
with an explicit absolute constant and the exact denominator and height decay. -/
theorem integral_norm_energyFourierKernel_half_le {c y E : ℝ}
    (hc : 0 < c) (hy : 0 < y) (hE : 0 ≤ E) (j J : ℤ) :
    (∫ t : ℝ, ‖energyFourierKernel c y (E : ℂ) j J (1 / 2 : ℂ) t‖) ≤
      2 * Real.pi ^ 2 * E / (c ^ 3 * Real.sqrt y) := by
  have hstd : Integrable (fun t : ℝ => (1 + (t / y) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div hy.ne'
  have hmass : (∫ t : ℝ, (1 + (t / y) ^ 2)⁻¹) = y * Real.pi := by
    calc
      _ = |y| • ∫ u : ℝ, (1 + u ^ 2)⁻¹ :=
        Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2)⁻¹) y
      _ = y * Real.pi := by
        rw [abs_of_pos hy]
        change y * (∫ u : ℝ, (1 + u ^ 2)⁻¹) = y * Real.pi
        rw [integral_univ_inv_one_add_sq]
  have hmajor : Integrable (fun t : ℝ => (2 * Real.pi * E) *
      ((1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * (1 + (t / y) ^ 2)⁻¹)) :=
    (hstd.const_mul ((1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ))).const_mul (2 * Real.pi * E)
  calc
    _ ≤ ∫ t : ℝ, (2 * Real.pi * E) *
        ((1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * (1 + (t / y) ^ 2)⁻¹) := by
      apply integral_mono (integrable_energyFourierKernel_half hc hy E j J).norm hmajor
      intro t
      exact (norm_energyFourierKernel_half_le hc hy hE j J t).trans
        (mul_le_mul_of_nonneg_left (height_three_halves_le_cauchy hc hy t) (by positivity))
    _ = (2 * Real.pi * E) *
        ((1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * (y * Real.pi)) := by
      rw [integral_const_mul, integral_const_mul, hmass]
    _ = (2 * Real.pi * E) *
        (((1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * y) * Real.pi) := by ring
    _ = _ := by rw [height_three_halves_scale hc hy]; ring

end GapFamily.Analytic.PoincareEnergyFourier
