import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace GapFamily.Analytic.FormTruncation
open MeasureTheory Filter
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Genuine pointwise domination of differences gives convergence of actual L² classes. -/
theorem tendsto_L2_of_dominated
    (fseq : ℕ → Lp ℂ 2 μ) (f : Lp ℂ 2 μ) (g : α → ℝ)
    (hg : Integrable (fun x => g x ^ 2) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖fseq n x - f x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => fseq n x) atTop (𝓝 (f x))) :
    Tendsto fseq atTop (𝓝 f) := by
  have hsq : Tendsto (fun n => ∫ x, ‖fseq n x - f x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have hd := tendsto_integral_of_dominated_convergence
      (F := fun n x => ‖fseq n x - f x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => g x ^ 2)
      (fun n => ((Lp.aestronglyMeasurable (fseq n)).sub (Lp.aestronglyMeasurable f)).norm.pow 2)
      hg
      (fun n => (hbound n).mono fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hx 2)
      (hlim.mono fun x hx => by simpa using ((hx.sub (tendsto_const_nhds (x := f x))).norm.pow 2))
    simpa only [integral_zero] using hd
  have hnorm (n : ℕ) : ‖fseq n - f‖ ^ 2 = ∫ x, ‖fseq n x - f x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (fseq n) f] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
    rfl
  have hnormsq : Tendsto (fun n => ‖fseq n - f‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hnorm] using hsq
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hnormsq
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero,
    dist_eq_norm] using hsqrt

/-- Cutoffs which eventually agree pointwise converge under an actual L² bound. -/
theorem tendsto_L2_of_eventuallyEq_and_bound
    (fseq : ℕ → Lp ℂ 2 μ) (f : Lp ℂ 2 μ) (g : α → ℝ)
    (hg : Integrable (fun x => g x ^ 2) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖fseq n x - f x‖ ≤ g x)
    (heq : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, fseq n x = f x) :
    Tendsto fseq atTop (𝓝 f) := by
  apply tendsto_L2_of_dominated fseq f g hg hbound
  filter_upwards [heq] with x hx
  have hx' : (fun n => fseq n x) =ᶠ[atTop] (fun _ => f x) := hx
  exact tendsto_const_nhds.congr' hx'.symm

end GapFamily.Analytic.FormTruncation
