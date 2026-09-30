import GapFamily.Analytic.Poincare.Fourier.PoincareFourierKernel

/-!
The literal nonzero-energy correction to the unrolled Fourier kernel.
The exponential difference supplies one additional power of the transformed height.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier

open Set MeasureTheory

/-- The actual nonzero-energy correction, including both Fourier phases. -/
def energyFourierKernel (c y : ℝ) (E : ℂ) (j J : ℤ) (s : ℂ) (t : ℝ) : ℂ :=
  PoincareFourierUnfold.fourierKernel c y j J s t *
    (Complex.exp (-2 * (Real.pi : ℂ) * E *
      ((y / (c ^ 2 * (t ^ 2 + y ^ 2)) : ℝ) : ℂ)) - 1)

/-- Continuity of the actual energy correction requires no half-plane assumption. -/
theorem continuous_energyFourierKernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) (s : ℂ) : Continuous (energyFourierKernel c y E j J s) := by
  have hd : Continuous (fun t : ℝ => c ^ 2 * (t ^ 2 + y ^ 2)) := by fun_prop
  have hdn (t : ℝ) : c ^ 2 * (t ^ 2 + y ^ 2) ≠ 0 := by positivity
  have hb : Continuous (fun t : ℝ => y / (c ^ 2 * (t ^ 2 + y ^ 2))) :=
    continuous_const.div hd hdn
  have he : Continuous (fun t : ℝ => Complex.exp (-2 * (Real.pi : ℂ) * E *
      ((y / (c ^ 2 * (t ^ 2 + y ^ 2)) : ℝ) : ℂ)) - 1) :=
    ((continuous_const.mul (Complex.continuous_ofReal.comp hb)).cexp).sub continuous_const
  exact (PoincareFourierUnfold.continuous_fourierKernel hc hy j J s).mul he

private theorem height_le {c y : ℝ} (hc : 0 < c) (hy : 0 < y) (t : ℝ) :
    y / (c ^ 2 * (t ^ 2 + y ^ 2)) ≤ 1 / (c ^ 2 * y) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg t, sq_pos_of_pos hc]

/-- A global majorant for arbitrary complex energy; the exponent gains one. -/
theorem norm_energyFourierKernel_le {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) (s : ℂ) (t : ℝ) :
    ‖energyFourierKernel c y E j J s t‖ ≤
      (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖ * (1 / (c ^ 2 * y)))) *
        (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ (s.re + 1) := by
  let p : ℝ := y / (c ^ 2 * (t ^ 2 + y ^ 2))
  have hp : 0 < p := by dsimp [p]; positivity
  have hnorm : ‖-2 * (Real.pi : ℂ) * E * (p : ℂ)‖ = 2 * Real.pi * ‖E‖ * p := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hp]
  have hexp : ‖Complex.exp (-2 * (Real.pi : ℂ) * E * (p : ℂ)) - 1‖ ≤
      (2 * Real.pi * ‖E‖ * p) * Real.exp (2 * Real.pi * ‖E‖ * p) := by
    simpa only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_one, hnorm] using Complex.norm_exp_sub_sum_le_norm_mul_exp
      (-2 * (Real.pi : ℂ) * E * (p : ℂ)) 1
  have hmono : Real.exp (2 * Real.pi * ‖E‖ * p) ≤
      Real.exp (2 * Real.pi * ‖E‖ * (1 / (c ^ 2 * y))) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (height_le hc hy t) (by positivity))
  rw [energyFourierKernel, norm_mul,
    PoincareFourierUnfold.norm_fourierKernel hc hy]
  change p ^ s.re * ‖Complex.exp (-2 * (Real.pi : ℂ) * E * (p : ℂ)) - 1‖ ≤ _
  calc
    _ ≤ p ^ s.re * ((2 * Real.pi * ‖E‖ * p) *
        Real.exp (2 * Real.pi * ‖E‖ * (1 / (c ^ 2 * y)))) :=
      mul_le_mul_of_nonneg_left
        (hexp.trans (mul_le_mul_of_nonneg_left hmono (by positivity)))
        (Real.rpow_nonneg hp.le _)
    _ = _ := by change _ = _ * p ^ (s.re + 1); rw [Real.rpow_add_one hp.ne']; ring

private theorem height_rpow_factor {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (σ t : ℝ) :
    (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ σ =
      (1 / (c ^ 2 * y)) ^ σ * (1 + (t / y) ^ 2) ^ (-σ) := by
  have hq : t ^ 2 + y ^ 2 ≠ 0 := by positivity
  have he : y / (c ^ 2 * (t ^ 2 + y ^ 2)) =
      (1 / (c ^ 2 * y)) / (1 + (t / y) ^ 2) := by
    field_simp [hc.ne', hy.ne', hq]
    ring
  rw [he, Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
    div_eq_mul_inv]

private theorem integrable_height_rpow {c y σ : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hσ : 1 / 2 < σ) :
    Integrable (fun t : ℝ => (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ σ) volume := by
  have hstd : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-σ)) volume := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * σ)
      (by simpa using (show (1 : ℝ) < 2 * σ by linarith))
    convert h using 1
    funext t
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  apply ((hstd.comp_div hy.ne').const_mul ((1 / (c ^ 2 * y)) ^ σ)).congr
  filter_upwards with t
  exact (height_rpow_factor hc hy σ t).symm

/-- Ordinary Bochner integrability of the actual energy kernel in Re(s)>0. -/
theorem integrable_energyFourierKernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (energyFourierKernel c y E j J s) volume := by
  have hpow := integrable_height_rpow hc hy (σ := s.re + 1) (by linarith)
  apply (hpow.const_mul
    (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖ * (1 / (c ^ 2 * y))))).mono'
    (continuous_energyFourierKernel hc hy E j J s).aestronglyMeasurable
  filter_upwards with t
  exact norm_energyFourierKernel_le hc hy E j J s t

/-- The literal energy-correction kernel unfolds over each translated unit partition. -/
theorem hasSum_intervalIntegral_energyFourierKernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E : ℂ) (j J : ℤ) {s : ℂ} (hs : 0 < s.re) (a : ℝ) :
    HasSum (fun k : ℤ => ∫ x in (0 : ℝ)..1, energyFourierKernel c y E j J s (x + a + k))
      (∫ t : ℝ, energyFourierKernel c y E j J s t) :=
  PoincareFourierUnfold.hasSum_integral_shifted_unitInterval
    (integrable_energyFourierKernel hc hy E j J hs) a

/-- The ordinary integrated norms of these actual shifted terms are summable. -/
theorem summable_intervalIntegral_norm_energyFourierKernel {c y : ℝ}
    (hc : 0 < c) (hy : 0 < y) (E : ℂ) (j J : ℤ) {s : ℂ} (hs : 0 < s.re) (a : ℝ) :
    Summable (fun k : ℤ => ∫ x in (0 : ℝ)..1,
      ‖energyFourierKernel c y E j J s (x + a + k)‖) :=
  (PoincareFourierUnfold.hasSum_integral_shifted_unitInterval
    (integrable_energyFourierKernel hc hy E j J hs).norm a).summable

end GapFamily.Analytic.PoincareEnergyFourier
