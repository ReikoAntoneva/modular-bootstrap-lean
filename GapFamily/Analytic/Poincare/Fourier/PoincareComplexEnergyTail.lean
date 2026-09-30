import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierTailSum

/-! The ordinary energy correction decays at the cusp for every complex energy,
including the negative energies of the vacuum seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory Filter
open scoped Topology

/-- A fixed complex energy has an ordinary integrated majorant at all cusp heights.
The bound is uniform in the two integer spins. -/
theorem integral_norm_energyFourierKernel_half_complex_le {c y : ℝ}
    (hc : 1 ≤ c) (hy : 1 ≤ y) (E : ℂ) (j J : ℤ) :
    (∫ t : ℝ, ‖energyFourierKernel c y E j J (1 / 2 : ℂ) t‖) ≤
      (2 * Real.pi ^ 2 * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) /
        (c ^ 3 * Real.sqrt y) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hcy : 1 ≤ c ^ 2 * y :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc) hy
  have hinv : 1 / (c ^ 2 * y) ≤ (1 : ℝ) :=
    (div_le_one (by positivity)).2 hcy
  have he : Real.exp (2 * Real.pi * ‖E‖ * (1 / (c ^ 2 * y))) ≤
      Real.exp (2 * Real.pi * ‖E‖) := by
    apply Real.exp_le_exp.mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ 2 * Real.pi * ‖E‖ by positivity)
  have hkernel (t : ℝ) : ‖energyFourierKernel c y E j J (1 / 2 : ℂ) t‖ ≤
      (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) *
        ((1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * (1 + (t / y) ^ 2)⁻¹) := by
    calc
      _ ≤ (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖ *
          (1 / (c ^ 2 * y)))) *
          (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ (3 / 2 : ℝ) := by
        simpa only [show (1 / 2 : ℂ).re + 1 = (3 / 2 : ℝ) by norm_num] using
          norm_energyFourierKernel_le hc0 hy0 E j J (1 / 2 : ℂ) t
      _ ≤ (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) *
          (y / (c ^ 2 * (t ^ 2 + y ^ 2))) ^ (3 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (height_three_halves_le_cauchy hc0 hy0 t)
        (by positivity)
  have hstd : Integrable (fun t : ℝ => (1 + (t / y) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div hy0.ne'
  have hmass : (∫ t : ℝ, (1 + (t / y) ^ 2)⁻¹) = y * Real.pi := by
    calc
      _ = |y| • ∫ u : ℝ, (1 + u ^ 2)⁻¹ :=
        Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2)⁻¹) y
      _ = y * Real.pi := by
        rw [abs_of_pos hy0]
        change y * (∫ u : ℝ, (1 + u ^ 2)⁻¹) = y * Real.pi
        rw [integral_univ_inv_one_add_sq]
  have hmajor : Integrable (fun t : ℝ =>
      (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) *
        ((1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * (1 + (t / y) ^ 2)⁻¹)) :=
    (hstd.const_mul ((1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ))).const_mul _
  calc
    _ ≤ ∫ t : ℝ, (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) *
        ((1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * (1 + (t / y) ^ 2)⁻¹) :=
      integral_mono (integrable_energyFourierKernel hc0 hy0 E j J (by norm_num)).norm
        hmajor hkernel
    _ = (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) *
        ((1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * (y * Real.pi)) := by
      rw [integral_const_mul, integral_const_mul, hmass]
    _ = (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) *
        (((1 / (c ^ 2 * y)) ^ (3 / 2 : ℝ) * y) * Real.pi) := by ring
    _ = _ := by rw [height_three_halves_scale hc0 hy0]; ring

/-- An explicit summable bound for the full energy correction at arbitrary complex energy. -/
theorem norm_energyFourier_denominator_sum_half_complex_le {y : ℝ} (hy : 1 ≤ y)
    (E : ℂ) (j J : ℤ) :
    ‖∑' n : ℕ, kloostermanSum j J n *
      ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J (1 / 2 : ℂ) t‖ ≤
    ((2 * Real.pi ^ 2 * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) / Real.sqrt y) *
      ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  let A : ℝ := (2 * Real.pi ^ 2 * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) / Real.sqrt y
  have hg : Summable (fun n : ℕ => A * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    summable_energyFourier_denominator_majorant.mul_left A
  have hf := summable_norm_kloosterman_energyFourier_threshold y hy0 E j J
  calc
    _ ≤ ∑' n : ℕ, ‖kloostermanSum j J n *
        ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J (1 / 2 : ℂ) t‖ :=
      norm_tsum_le_tsum_norm hf
    _ ≤ ∑' n : ℕ, A * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      apply Summable.tsum_le_tsum _ hf hg
      intro n
      have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hnrm := (norm_integral_le_integral_norm
        (energyFourierKernel (n + 1 : ℕ) y E j J (1 / 2 : ℂ))).trans
        (integral_norm_energyFourierKernel_half_complex_le hn1 hy E j J)
      rw [norm_mul]
      calc
        _ ≤ ((n + 1 : ℕ) : ℝ) *
            ((2 * Real.pi ^ 2 * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) /
              (((n + 1 : ℕ) : ℝ) ^ 3 * Real.sqrt y)) :=
          mul_le_mul (by simpa using norm_kloostermanSum_le j J n) hnrm
            (norm_nonneg _) hn.le
        _ = A * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
          dsimp [A]
          field_simp [hn.ne', (Real.sqrt_pos.2 hy0).ne']
    _ = _ := by rw [tsum_mul_left]

/-- After division by sqrt(height), the actual energy correction vanishes for every
complex input energy, so it cannot alter the scalar threshold normalization. -/
theorem energyFourier_denominator_sum_div_sqrt_tendsto_zero_complex (E : ℂ) (j J : ℤ) :
    Tendsto (fun y : ℝ => (∑' n : ℕ, kloostermanSum j J n *
      ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y E j J (1 / 2 : ℂ) t) /
        (Real.sqrt y : ℂ)) atTop (𝓝 0) := by
  let A : ℝ := (2 * Real.pi ^ 2 * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) *
    ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2
  apply squeeze_zero_norm' (a := fun y : ℝ => A / y)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg y)]
    calc
      _ ≤ (((2 * Real.pi ^ 2 * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖)) / Real.sqrt y) *
          ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2) / Real.sqrt y :=
        div_le_div_of_nonneg_right (norm_energyFourier_denominator_sum_half_complex_le hy E j J)
          (Real.sqrt_nonneg y)
      _ = A / y := by
        rw [div_mul_eq_mul_div, div_div, Real.mul_self_sqrt (by linarith : 0 ≤ y)]
  · exact tendsto_id.const_div_atTop A

end GapFamily.Analytic.PoincareEnergyFourier
