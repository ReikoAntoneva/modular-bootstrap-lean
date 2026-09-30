import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace GapFamily.Analytic.DominatedL2

open Set Filter MeasureTheory
open scoped Topology

variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [TopologicalSpace Y]

private theorem norm_L2_sq_integral_local (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  exact real_inner_self_eq_norm_sq (u x)

/-- Pointwise continuity of representatives with a common local L² bound implies
norm continuity of the represented L² vectors. -/
theorem continuousAt_L2_of_dominated
    (u : Y → Lp ℂ 2 μ) (F : Y → X → ℂ) (y₀ : Y) (S : Set Y) (B : X → ℝ)
    [(𝓝 y₀).IsCountablyGenerated]
    (hS : S ∈ 𝓝 y₀)
    (hrep : ∀ y ∈ S, (u y : X → ℂ) =ᵐ[μ] F y)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt (fun y => F y x) y₀)
    (hbound : ∀ᵐ x ∂μ, ∀ y ∈ S, ‖F y x‖ ≤ B x)
    (hB : MemLp B 2 μ) : ContinuousAt u y₀ := by
  have hy₀ : y₀ ∈ S := mem_of_mem_nhds hS
  have hm (y : Y) (hy : y ∈ S) : AEStronglyMeasurable (F y) μ :=
    (Lp.aestronglyMeasurable (u y)).congr (hrep y hy)
  have hi : Tendsto (fun y => ∫ x, ‖F y x - F y₀ x‖ ^ 2 ∂μ)
      (𝓝 y₀) (𝓝 (0 : ℝ)) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 y₀)
      (F := fun y x => ‖F y x - F y₀ x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => 4 * B x ^ 2) ?_ ?_ (hB.integrable_sq.const_mul 4) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [hS] with y hy
      exact ((hm y hy).sub (hm y₀ hy₀)).norm.pow 2
    · filter_upwards [hS] with y hy
      filter_upwards [hbound] with x hx
      have hb0 : 0 ≤ B x := (norm_nonneg (F y₀ x)).trans (hx y₀ hy₀)
      have hd : ‖F y x - F y₀ x‖ ≤ 2 * B x :=
        (norm_sub_le _ _).trans (by linarith [hx y hy, hx y₀ hy₀])
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (F y x - F y₀ x)]
    · filter_upwards [hcont] with x hx
      simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        ((hx.tendsto.sub_const (F y₀ x)).norm.pow 2)
  have he (y : Y) (hy : y ∈ S) :
      ‖u y - u y₀‖ ^ 2 = ∫ x, ‖F y x - F y₀ x‖ ^ 2 ∂μ := by
    rw [norm_L2_sq_integral_local]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u y) (u y₀), hrep y hy, hrep y₀ hy₀]
      with x hsub hyrep hy₀rep
    simp only [hsub, Pi.sub_apply, hyrep, hy₀rep]
  have hsq : Tendsto (fun y => ‖u y - u y₀‖ ^ 2) (𝓝 y₀) (𝓝 (0 : ℝ)) :=
    hi.congr' ((show ∀ᶠ y in 𝓝 y₀, y ∈ S from hS).mono
      (fun y hy => (he y hy).symm))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

end GapFamily.Analytic.DominatedL2
