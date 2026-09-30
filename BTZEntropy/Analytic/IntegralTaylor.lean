import BTZEntropy.Analytic.IntegralTaylorDomination
import BTZEntropy.Analytic.IntegralTaylorPointwise

/-! Parameterwise Taylor expansion under an integral. All differentiability
is checked before integration. The measure may already be restricted to a
parameter-dependent domain. -/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators

namespace BTZEntropy.Analytic

/-- Integrated Taylor polynomial, with the actual ordinary derivative jets. -/
def integralTaylorPolynomial {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (F : ℝ → α → ℂ) (N : ℕ) (ε : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), (ε ^ n / (n.factorial : ℝ)) •
    (∫ t, iteratedDeriv n (fun e => F e t) 0 ∂μ)

/-- Pointwise smoothness and an integrable highest-derivative bound imply
both integrability at the displaced parameter and the sharp factorial
Taylor bound. No differentiability of the parameter integral is assumed. -/
theorem integrable_and_norm_integral_sub_taylor_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℝ → α → ℂ} {N : ℕ} {ε : ℝ} {M : α → ℝ}
    (hF : AEStronglyMeasurable (F ε) μ)
    (hjet : ∀ n ≤ N, Integrable (fun t => iteratedDeriv n (fun e => F e t) 0) μ)
    (hM : Integrable M μ)
    (hsmooth : ∀ᵐ t ∂μ, ∀ e ∈ uIcc 0 ε,
      ContDiffAt ℝ (N + 1 : ℕ) (fun s => F s t) e)
    (hderiv : ∀ᵐ t ∂μ, ∀ e ∈ uIcc 0 ε,
      ‖iteratedDeriv (N + 1) (fun s => F s t) e‖ ≤ M t) :
    Integrable (F ε) μ ∧
      ‖(∫ t, F ε t ∂μ) - integralTaylorPolynomial μ F N ε‖ ≤
        (|ε| ^ (N + 1) / ((N + 1).factorial : ℝ)) * ∫ t, M t ∂μ := by
  apply integral_sub_sum_norm_le (Finset.range (N + 1))
    (fun n => ε ^ n / (n.factorial : ℝ))
    (|ε| ^ (N + 1) / ((N + 1).factorial : ℝ)) hF
    (fun n hn => hjet n (by simpa using Finset.mem_range.mp hn)) hM
  filter_upwards [hsmooth, hderiv] with t ht hd
  exact norm_sub_taylorJetPolynomial_le ht hd

/-- Exact integral expansion with a controlled remainder. -/
theorem integral_eq_taylor_add_remainder
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℝ → α → ℂ} {N : ℕ} {ε : ℝ} {M : α → ℝ}
    (hF : AEStronglyMeasurable (F ε) μ)
    (hjet : ∀ n ≤ N, Integrable (fun t => iteratedDeriv n (fun e => F e t) 0) μ)
    (hM : Integrable M μ)
    (hsmooth : ∀ᵐ t ∂μ, ∀ e ∈ uIcc 0 ε,
      ContDiffAt ℝ (N + 1 : ℕ) (fun s => F s t) e)
    (hderiv : ∀ᵐ t ∂μ, ∀ e ∈ uIcc 0 ε,
      ‖iteratedDeriv (N + 1) (fun s => F s t) e‖ ≤ M t) :
    ∃ R : ℂ, (∫ t, F ε t ∂μ) = integralTaylorPolynomial μ F N ε + R ∧
      ‖R‖ ≤ (|ε| ^ (N + 1) / ((N + 1).factorial : ℝ)) * ∫ t, M t ∂μ := by
  refine ⟨(∫ t, F ε t ∂μ) - integralTaylorPolynomial μ F N ε, by abel, ?_⟩
  exact (integrable_and_norm_integral_sub_taylor_le hF hjet hM hsmooth hderiv).2

/-- On any measurable integration domain, a nonnegative whole-space
majorant controls the remainder. The domain may depend on the parameter. -/
theorem norm_setIntegral_sub_taylor_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℝ → α → ℂ} {N : ℕ} {ε : ℝ} {M : α → ℝ}
    {S : Set α} (hS : MeasurableSet S)
    (hF : AEStronglyMeasurable (F ε) (μ.restrict S))
    (hjet : ∀ n ≤ N, IntegrableOn (fun t => iteratedDeriv n (fun e => F e t) 0) S μ)
    (hM : Integrable M μ) (hMnonneg : ∀ᵐ t ∂μ, 0 ≤ M t)
    (hsmooth : ∀ t ∈ S, ∀ e ∈ uIcc 0 ε,
      ContDiffAt ℝ (N + 1 : ℕ) (fun s => F s t) e)
    (hderiv : ∀ t ∈ S, ∀ e ∈ uIcc 0 ε,
      ‖iteratedDeriv (N + 1) (fun s => F s t) e‖ ≤ M t) :
    IntegrableOn (F ε) S μ ∧
      ‖(∫ t in S, F ε t ∂μ) - integralTaylorPolynomial (μ.restrict S) F N ε‖ ≤
        (|ε| ^ (N + 1) / ((N + 1).factorial : ℝ)) * ∫ t, M t ∂μ := by
  have h := integrable_and_norm_integral_sub_taylor_le hF hjet hM.integrableOn
    ((ae_restrict_mem hS).mono fun t ht => hsmooth t ht)
    ((ae_restrict_mem hS).mono fun t ht => hderiv t ht)
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hM hMnonneg) (by positivity)

end BTZEntropy.Analytic
