import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierTailBound
import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierThreshold

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory Filter
open scoped Topology

/-- The reciprocal-square denominator majorant is an ordinary convergent series. -/
theorem summable_energyFourier_denominator_majorant :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  exact (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))

/-- A uniform integrated bound for the actual full positive-denominator correction. -/
theorem norm_energyFourier_denominator_sum_half_le {y E : ℝ} (hy : 0 < y)
    (hE : 0 ≤ E) (j J : ℤ) :
    ‖∑' n : ℕ, kloostermanSum j J n *
      ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y (E : ℂ) j J (1 / 2 : ℂ) t‖ ≤
    (2 * Real.pi ^ 2 * E / Real.sqrt y) *
      ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  let A : ℝ := 2 * Real.pi ^ 2 * E / Real.sqrt y
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hg : Summable (fun n : ℕ => A * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    summable_energyFourier_denominator_majorant.mul_left A
  have hf := summable_norm_kloosterman_energyFourier_threshold y hy (E : ℂ) j J
  calc
    _ ≤ ∑' n : ℕ, ‖kloostermanSum j J n *
        ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y (E : ℂ) j J (1 / 2 : ℂ) t‖ :=
      norm_tsum_le_tsum_norm hf
    _ ≤ ∑' n : ℕ, A * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      apply Summable.tsum_le_tsum _ hf hg
      intro n
      have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hbound := integral_norm_energyFourierKernel_half_le hn hy hE j J
      have hnrm : ‖∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y (E : ℂ) j J
          (1 / 2 : ℂ) t‖ ≤ 2 * Real.pi ^ 2 * E /
            (((n + 1 : ℕ) : ℝ) ^ 3 * Real.sqrt y) :=
        (norm_integral_le_integral_norm _).trans hbound
      rw [norm_mul]
      calc
        _ ≤ ((n + 1 : ℕ) : ℝ) * (2 * Real.pi ^ 2 * E /
            (((n + 1 : ℕ) : ℝ) ^ 3 * Real.sqrt y)) := by
          apply mul_le_mul (by simpa using norm_kloostermanSum_le j J n) hnrm
            (norm_nonneg _) hn.le
        _ = A * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
          dsimp [A]
          field_simp [hn.ne', (Real.sqrt_pos.2 hy).ne']
    _ = _ := by rw [tsum_mul_left]

/-- The bound is uniform in both spins and in every nonnegative real energy. -/
theorem exists_energyFourier_denominator_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (y E : ℝ), 0 < y → 0 ≤ E → ∀ j J : ℤ,
      ‖∑' n : ℕ, kloostermanSum j J n *
        ∫ t : ℝ, energyFourierKernel (n + 1 : ℕ) y (E : ℂ) j J (1 / 2 : ℂ) t‖ ≤
          C * E / Real.sqrt y := by
  let B : ℝ := ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2
  have hB : 0 ≤ B := tsum_nonneg (fun n => by positivity)
  refine ⟨2 * Real.pi ^ 2 * B + 1, by positivity, ?_⟩
  intro y E hy hE j J
  calc
    _ ≤ (2 * Real.pi ^ 2 * E / Real.sqrt y) * B :=
      norm_energyFourier_denominator_sum_half_le hy hE j J
    _ ≤ (2 * Real.pi ^ 2 * B + 1) * E / Real.sqrt y := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg y)
      nlinarith

end GapFamily.Analytic.PoincareEnergyFourier
