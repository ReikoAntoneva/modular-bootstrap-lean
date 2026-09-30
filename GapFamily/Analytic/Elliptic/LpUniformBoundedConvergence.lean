import GapFamily.Analytic.Kernel.SchurIntegralOperator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace GapFamily.Analytic.LpUniformBoundedConvergence
open MeasureTheory Filter SchurIntegralOperator
open scoped Topology
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- Actual AE bounded convergence on a finite measure gives strong L² convergence.
The finite dominating function and the exact L² norm integral are both proved. -/
theorem tendsto_L2_of_ae_of_uniform_bound (u : ℕ → Lp ℂ 2 μ) (f : Lp ℂ 2 μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ ≤ M) (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ M)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    Tendsto u atTop (𝓝 f) := by
  have hi : Tendsto (fun n => ∫ x, ‖u n x - f x‖ ^ 2 ∂μ) atTop (𝓝 (0 : ℝ)) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ‖u n x - f x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun _ => 4 * M ^ 2) ?_ (integrable_const _) ?_ ?_
    · simpa only [integral_zero] using h
    · intro n
      exact ((Lp.aestronglyMeasurable (u n)).sub (Lp.aestronglyMeasurable f)).norm.pow 2
    · intro n
      filter_upwards [hu n, hf] with x hx hy
      have hb : ‖u n x - f x‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (u n x - f x)]
    · filter_upwards [hlim] with x hx
      simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        ((hx.sub_const (f x)).norm.pow 2)
  have he (n : ℕ) : ‖u n - f‖ ^ 2 = ∫ x, ‖u n x - f x‖ ^ 2 ∂μ := by
    rw [l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u n) f] with x hx
    simp only [hx, Pi.sub_apply]
  have hsq : Tendsto (fun n => ‖u n - f‖ ^ 2) atTop (𝓝 (0 : ℝ)) :=
    hi.congr' (Eventually.of_forall fun n => (he n).symm)
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

end GapFamily.Analytic.LpUniformBoundedConvergence
