import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic

/-! Integration of a finite pointwise approximation and its integrable
majorant. The integrability of the approximated function is a conclusion. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace BTZEntropy.Analytic

/-- A pointwise approximation by finitely many integrable functions passes
through the integral, with the same integrated majorant. -/
theorem integral_sub_sum_norm_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} {g : ℕ → α → ℂ} {M : α → ℝ}
    (S : Finset ℕ) (c : ℕ → ℝ) (A : ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hg : ∀ n ∈ S, Integrable (g n) μ) (hM : Integrable M μ)
    (hpoint : ∀ᵐ t ∂μ, ‖f t - ∑ n ∈ S, c n • g n t‖ ≤ A * M t) :
    Integrable f μ ∧
      ‖(∫ t, f t ∂μ) - ∑ n ∈ S, c n • (∫ t, g n t ∂μ)‖ ≤ A * ∫ t, M t ∂μ := by
  have hpoly : Integrable (fun t => ∑ n ∈ S, c n • g n t) μ :=
    integrable_finsetSum S (fun n hn => (hg n hn).smul (c n))
  have hrem : Integrable (fun t => f t - ∑ n ∈ S, c n • g n t) μ :=
    (hM.const_mul A).mono' (hf.sub hpoly.aestronglyMeasurable) hpoint
  have hfi : Integrable f μ := by
    convert hrem.add hpoly using 1
    funext t
    exact (sub_add_cancel _ _).symm
  refine ⟨hfi, ?_⟩
  have hbound := norm_integral_le_of_norm_le (hM.const_mul A) hpoint
  rw [integral_sub hfi hpoly,
    integral_finsetSum S (f := fun n t => c n • g n t) (fun n hn => (hg n hn).smul (c n)),
    integral_const_mul] at hbound
  simpa only [integral_smul] using hbound

end BTZEntropy.Analytic
