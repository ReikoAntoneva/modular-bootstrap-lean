import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierTailSum
import GapFamily.Analytic.Poincare.Fourier.PoincareScalarFourierZero

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory Filter
open scoped Topology

/-- Dividing the actual denominator correction by sqrt(height) makes it vanish at infinity. -/
theorem energyFourier_denominator_sum_div_sqrt_tendsto_zero {E : ℝ} (hE : 0 ≤ E)
    (j J : ℤ) :
    Tendsto (fun y : ℝ => (∑' n : ℕ, kloostermanSum j J n *
      ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y (E : ℂ) j J (1 / 2 : ℂ) t) /
        (Real.sqrt y : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_energyFourier_denominator_sum_bound
  apply squeeze_zero_norm' (a := fun y : ℝ => C * E / y)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg y)]
    calc
      _ ≤ (C * E / Real.sqrt y) / Real.sqrt y :=
        div_le_div_of_nonneg_right (hb y E hy hE j J) (Real.sqrt_nonneg y)
      _ = C * E / y := by rw [div_div, Real.mul_self_sqrt hy.le]
  · exact tendsto_id.const_div_atTop (C * E)

/-- The actual scalar coefficient has a uniform O(E/y) normalized error, for every E>=0. -/
theorem exists_scalarThresholdFourier_normalized_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (y E : ℝ) (hy : 0 < y), 0 ≤ E →
      ‖generalThresholdFourierCoefficient y hy (E : ℂ) 0 0 / (Real.sqrt y : ℂ) -
        ((Real.exp (-2 * Real.pi * E * y) : ℝ) : ℂ) + 1‖ ≤ C * E / y := by
  obtain ⟨C, hC, hb⟩ := exists_energyFourier_denominator_sum_bound
  refine ⟨C, hC, ?_⟩
  intro y E hy hE
  have hs : (Real.sqrt y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.2 hy).ne'
  have hp : (y : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt y : ℂ) := by
    calc
      (y : ℂ) ^ (1 / 2 : ℂ) = ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        simpa using (Complex.ofReal_cpow hy.le (1 / 2 : ℝ)).symm
      _ = _ := by rw [← Real.sqrt_eq_rpow]
  have he : Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) =
      (Real.exp (-2 * Real.pi * E * y) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [generalThresholdFourierCoefficient_eq_base_add_kloosterman,
    thresholdFourierCoefficient_zero_zero, zero_add, energyFourierDirect, ite_eq_left rfl,
    hp, he, add_div, mul_div_cancel_left₀ _ hs]
  have halg (a b : ℂ) : (a - 1 + b) - a + 1 = b := by ring
  rw [halg, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg y)]
  calc
    _ ≤ (C * E / Real.sqrt y) / Real.sqrt y :=
      div_le_div_of_nonneg_right (hb y E hy hE 0 0) (Real.sqrt_nonneg y)
    _ = C * E / y := by rw [div_div, Real.mul_self_sqrt hy.le]

/-- The scalar threshold Fourier coefficient extracts the source normalization -1 for E>0.
This is an ordinary coefficient asymptotic, not an inverse-Laplace measure identity. -/
theorem scalarThresholdFourier_div_sqrt_tendsto_neg_one {E : ℝ} (hE : 0 < E) :
    Tendsto (fun y : ℝ => if hy : 0 < y then
      generalThresholdFourierCoefficient y hy (E : ℂ) 0 0 / (Real.sqrt y : ℂ)
      else 0) atTop (𝓝 (-1 : ℂ)) := by
  obtain ⟨C, hC, hb⟩ := exists_scalarThresholdFourier_normalized_error_bound
  let F : ℝ → ℂ := fun y => if hy : 0 < y then
    generalThresholdFourierCoefficient y hy (E : ℂ) 0 0 / (Real.sqrt y : ℂ) else 0
  have herr : Tendsto (fun y => F y - (Real.exp (-2 * Real.pi * E * y) : ℂ) + 1)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun y : ℝ => C * E / y)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      simpa only [F, dite_eq_left hy] using hb y E hy hE.le
    · exact tendsto_id.const_div_atTop (C * E)
  have he : Tendsto (fun y : ℝ => Real.exp (-2 * Real.pi * E * y)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos] :
        -2 * Real.pi * E < 0))
  have hec : Tendsto (fun y : ℝ => (Real.exp (-2 * Real.pi * E * y) : ℂ))
      atTop (𝓝 0) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp he
  have h := (herr.add hec).sub_const (1 : ℂ)
  convert h using 1
  · funext y
    dsimp [F]
    ring
  · norm_num

end GapFamily.Analytic.PoincareEnergyFourier
