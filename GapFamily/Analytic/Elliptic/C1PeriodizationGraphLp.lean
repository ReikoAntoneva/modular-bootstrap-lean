import GapFamily.Analytic.Kernel.SchurIntegralOperator
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace GapFamily.Analytic.C1Periodization
open MeasureTheory Filter SchurIntegralOperator
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- An actual square-integrable majorant upgrades almost-everywhere convergence of
raw complex functions to strong convergence of their actual L² classes. -/
theorem tendsto_toLp_of_dominated (u : ℕ → X → ℂ) (f : X → ℂ)
    (hu : ∀ n, MemLp (u n) 2 μ) (hf : MemLp f 2 μ)
    (B : X → ℝ) (hB : MemLp B 2 μ)
    (hub : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ ≤ B x)
    (hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hf.toLp f)) := by
  have hi : Tendsto (fun n => ∫ x, ‖u n x - f x‖ ^ 2 ∂μ) atTop (𝓝 (0 : ℝ)) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ‖u n x - f x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => 4 * B x ^ 2) ?_ (hB.integrable_sq.const_mul 4) ?_ ?_
    · simpa only [integral_zero] using h
    · intro n
      exact ((hu n).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 2
    · intro n
      filter_upwards [hub n, hfb] with x hx hy
      have hb : ‖u n x - f x‖ ≤ 2 * B x := (norm_sub_le _ _).trans (by linarith)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (u n x - f x)]
    · filter_upwards [hlim] with x hx
      simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        ((hx.sub_const (f x)).norm.pow 2)
  have he (n : ℕ) : ‖(hu n).toLp (u n) - hf.toLp f‖ ^ 2 =
      ∫ x, ‖u n x - f x‖ ^ 2 ∂μ := by
    rw [l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hu n).toLp (u n)) (hf.toLp f),
      (hu n).coeFn_toLp, hf.coeFn_toLp] with x hx hux hfx
    simp only [hx, Pi.sub_apply, hux, hfx]
  have hsq : Tendsto (fun n => ‖(hu n).toLp (u n) - hf.toLp f‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := hi.congr' (Eventually.of_forall fun n => (he n).symm)
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

/-- The same domination proves membership before forming the L² classes. -/
theorem exists_memLp_tendsto_toLp_of_dominated (u : ℕ → X → ℂ) (f : X → ℂ)
    (hu : ∀ n, AEStronglyMeasurable (u n) μ) (hf : AEStronglyMeasurable f μ)
    (B : X → ℝ) (hB : MemLp B 2 μ)
    (hub : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ ≤ B x)
    (hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    ∃ (huLp : ∀ n, MemLp (u n) 2 μ) (hfLp : MemLp f 2 μ),
      Tendsto (fun n => (huLp n).toLp (u n)) atTop (𝓝 (hfLp.toLp f)) := by
  have huLp : ∀ n, MemLp (u n) 2 μ := fun n => hB.mono' (hu n) (hub n)
  have hfLp : MemLp f 2 μ := hB.mono' hf hfb
  exact ⟨huLp, hfLp, tendsto_toLp_of_dominated u f huLp hfLp B hB hub hfb hlim⟩

end GapFamily.Analytic.C1Periodization
