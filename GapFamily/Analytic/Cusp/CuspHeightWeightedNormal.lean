import GapFamily.Analytic.Cusp.CuspHeightFundamentalDomain
import GapFamily.Analytic.Modular.ModularBoundary

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory
open scoped Topology

/-- The same quarter-weight normal bound holds almost everywhere for the actual modular measure. -/
theorem shifted_nonidentityPoincare_quarter_weight_majorant_ae :
    ∃ u : {q : CuspCoset // q ≠ identityCuspCoset} → ℝ,
      Summable u ∧ ∀ᵐ τ ∂modularMeasure,
        ∀ (J : ℤ) (q : {q : CuspCoset // q ≠ identityCuspCoset}) (κ : ℂ),
          ‖κ‖ ≤ (1 / 8 : ℝ) →
          τ.im ^ (1 / 4 : ℝ) * ‖complexPoincareTerm 0 J ((5 / 2 : ℂ) + κ) τ q‖ ≤ u q := by
  obtain ⟨u, hu, hbound⟩ := shifted_nonidentityPoincare_quarter_weight_majorant
  refine ⟨u, hu, ?_⟩
  filter_upwards [ae_mem_fdo] with τ hτ
  intro J q κ hκ
  exact hbound J q κ τ hκ (ModularGroup.fdo_subset_fd hτ)

/-- Actual weighted partial sums converge uniformly on the entire unbounded closed
fundamental domain and the fixed parameter disk simultaneously. -/
theorem shifted_nonidentityPoincare_quarter_weight_tendstoUniformlyOn (J : ℤ) :
    TendstoUniformlyOn
      (fun A : Finset {q : CuspCoset // q ≠ identityCuspCoset} =>
        fun p : ℂ × UpperHalfPlane => ∑ q ∈ A,
          ((p.2.im ^ (1 / 4 : ℝ) : ℝ) : ℂ) * complexPoincareTerm 0 J ((5 / 2 : ℂ) + p.1) p.2 q)
      (fun p : ℂ × UpperHalfPlane => ∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
        ((p.2.im ^ (1 / 4 : ℝ) : ℝ) : ℂ) * complexPoincareTerm 0 J ((5 / 2 : ℂ) + p.1) p.2 q)
      atTop {p : ℂ × UpperHalfPlane | ‖p.1‖ ≤ (1 / 8 : ℝ) ∧ p.2 ∈ ModularGroup.fd} := by
  obtain ⟨u, hu, hbound⟩ := shifted_nonidentityPoincare_quarter_weight_majorant
  apply tendstoUniformlyOn_tsum hu
  intro q p hp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg p.2.im_pos.le (1 / 4 : ℝ))]
  exact hbound J q p.1 p.2 hp.1 hp.2

end GapFamily.Analytic
