import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import BTZEntropy.Analytic.IntegralTaylorKernel

/-!
# Pointwise Taylor remainder with the factorial constant

The Taylor polynomial uses ambient derivatives. Pointwise smoothness along the
closed segment suffices for the integral remainder identity.
-/

noncomputable section

open scoped BigOperators Interval
open Set MeasureTheory

namespace BTZEntropy.Analytic

/-- The ambient Taylor jet at zero, evaluated at a real increment. -/
def taylorJetPolynomial (f : ℝ → ℂ) (N : ℕ) (ε : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), (ε ^ n / (n.factorial : ℝ)) • iteratedDeriv n f 0

@[simp]
theorem taylorJetPolynomial_zero (f : ℝ → ℂ) (N : ℕ) :
    taylorJetPolynomial f N 0 = f 0 := by
  unfold taylorJetPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro n hn hn0
    simp [zero_pow hn0]
  · simp

/-- Taylor's integral identity expressed with ambient derivatives. -/
theorem sub_taylorJetPolynomial_eq_integral {f : ℝ → ℂ} {N : ℕ} {ε : ℝ}
    (hf : ∀ s ∈ uIcc 0 ε, ContDiffAt ℝ (N + 1 : ℕ) f s) :
    f ε - taylorJetPolynomial f N ε =
      ∫ s in 0..ε, ((ε - s) ^ N / (N.factorial : ℝ)) •
        iteratedDeriv (N + 1) f s := by
  by_cases hε : ε = 0
  · simp [hε]
  have hs : UniqueDiffOn ℝ (uIcc 0 ε) := uniqueDiffOn_uIcc (Ne.symm hε)
  have hon : ContDiffOn ℝ (N + 1 : ℕ) f (uIcc 0 ε) :=
    fun s hs => (hf s hs).contDiffWithinAt
  have hpoly : taylorWithinEval f N (uIcc 0 ε) 0 ε =
      taylorJetPolynomial f N ε := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro n hn
    have hnN : n ≤ N + 1 := (Finset.mem_range.mp hn).le
    rw [iteratedDerivWithin_eq_iteratedDeriv hs
      ((hf 0 left_mem_uIcc).of_le (by exact_mod_cast hnN)) left_mem_uIcc]
    simp [sub_zero, div_eq_mul_inv, mul_comm]
  rw [← hpoly, taylor_integral_remainder hon]
  apply intervalIntegral.integral_congr
  intro s hs'
  dsimp only
  rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf s hs') hs']

/-- The sharp factorial remainder bound for a complex-valued real Taylor jet. -/
theorem norm_sub_taylorJetPolynomial_le {f : ℝ → ℂ} {N : ℕ} {ε M : ℝ}
    (hf : ∀ s ∈ uIcc 0 ε, ContDiffAt ℝ (N + 1 : ℕ) f s)
    (hM : ∀ s ∈ uIcc 0 ε, ‖iteratedDeriv (N + 1) f s‖ ≤ M) :
    ‖f ε - taylorJetPolynomial f N ε‖ ≤
      (|ε| ^ (N + 1) / ((N + 1).factorial : ℝ)) * M := by
  calc
    ‖f ε - taylorJetPolynomial f N ε‖ =
        ‖∫ s in min 0 ε..max 0 ε, ((ε - s) ^ N / (N.factorial : ℝ)) •
          iteratedDeriv (N + 1) f s‖ := by
      rw [sub_taylorJetPolynomial_eq_integral hf, intervalIntegral.norm_integral_min_max]
    _ ≤ ∫ s in min 0 ε..max 0 ε, (|ε - s| ^ N / (N.factorial : ℝ)) * M := by
      apply intervalIntegral.norm_integral_le_of_norm_le min_le_max
      · apply Filter.Eventually.of_forall
        intro s hs
        simp only [norm_smul, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_left (hM s ⟨hs.1.le, hs.2⟩)
          (div_nonneg (pow_nonneg (abs_nonneg _) _) (Nat.cast_nonneg _))
      · exact (by fun_prop : Continuous
          (fun s : ℝ => (|ε - s| ^ N / (N.factorial : ℝ)) * M)).intervalIntegrable _ _
    _ = (|ε| ^ (N + 1) / ((N + 1).factorial : ℝ)) * M := by
      rw [intervalIntegral.integral_mul_const, integral_abs_taylorKernel]

end BTZEntropy.Analytic
