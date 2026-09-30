import BTZEntropy.Analytic.IntegralTaylor

/-! Restoring whole-space Taylor coefficients after expanding on a moving
integration domain. The extra error is the norm integral of the omitted jets. -/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators

namespace BTZEntropy.Analytic

/-- Omitted coefficient tails bound the difference between the restricted
and whole-space integrated Taylor polynomials. -/
theorem norm_integralTaylorPolynomial_restrict_sub_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℝ → α → ℂ} {N : ℕ} {ε : ℝ} {S : Set α}
    (hS : MeasurableSet S)
    (hjet : ∀ n ≤ N, Integrable (fun t => iteratedDeriv n (fun e => F e t) 0) μ) :
    ‖integralTaylorPolynomial (μ.restrict S) F N ε - integralTaylorPolynomial μ F N ε‖ ≤
      ∑ n ∈ Finset.range (N + 1), (|ε| ^ n / (n.factorial : ℝ)) *
        ∫ t in Sᶜ, ‖iteratedDeriv n (fun e => F e t) 0‖ ∂μ := by
  rw [integralTaylorPolynomial, integralTaylorPolynomial, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [norm_sub_rev, ← setIntegral_compl hS (hjet n (by simpa using Finset.mem_range.mp hn))]
  exact norm_integral_le_integral_norm _

/-- Taylor expansion on a measurable domain with whole-space coefficients.
The two errors are the integrated local remainder and the omitted jet tails. -/
theorem norm_setIntegral_sub_whole_taylor_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℝ → α → ℂ} {N : ℕ} {ε : ℝ} {M : α → ℝ}
    {S : Set α} (hS : MeasurableSet S)
    (hF : AEStronglyMeasurable (F ε) (μ.restrict S))
    (hjet : ∀ n ≤ N, Integrable (fun t => iteratedDeriv n (fun e => F e t) 0) μ)
    (hM : Integrable M μ) (hMnonneg : ∀ᵐ t ∂μ, 0 ≤ M t)
    (hsmooth : ∀ t ∈ S, ∀ e ∈ uIcc 0 ε,
      ContDiffAt ℝ (N + 1 : ℕ) (fun s => F s t) e)
    (hderiv : ∀ t ∈ S, ∀ e ∈ uIcc 0 ε,
      ‖iteratedDeriv (N + 1) (fun s => F s t) e‖ ≤ M t) :
    IntegrableOn (F ε) S μ ∧
      ‖(∫ t in S, F ε t ∂μ) - integralTaylorPolynomial μ F N ε‖ ≤
        (|ε| ^ (N + 1) / ((N + 1).factorial : ℝ)) * (∫ t, M t ∂μ) +
        ∑ n ∈ Finset.range (N + 1), (|ε| ^ n / (n.factorial : ℝ)) *
          ∫ t in Sᶜ, ‖iteratedDeriv n (fun e => F e t) 0‖ ∂μ := by
  have hlocal := norm_setIntegral_sub_taylor_le hS hF
    (fun n hn => (hjet n hn).integrableOn) hM hMnonneg hsmooth hderiv
  refine ⟨hlocal.1, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub (∫ t in S, F ε t ∂μ)
    (integralTaylorPolynomial (μ.restrict S) F N ε)
    (integralTaylorPolynomial μ F N ε)).trans
      (add_le_add hlocal.2 (norm_integralTaylorPolynomial_restrict_sub_le hS hjet))

end BTZEntropy.Analytic
