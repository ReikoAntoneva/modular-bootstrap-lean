import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Integration after finite moment cancellation

The two positive measures can be the positive and negative Jordan parts of a
signed measure. Every cancellation uses explicit integrability hypotheses.
The analytic approximation bound is supplied separately.
-/

open MeasureTheory Set
open scoped BigOperators

namespace GapFamily.Analytic

/-- Real monomial integrability is exactly enough for the complex-valued
monomials used by Taylor expansion. -/
theorem integrable_complex_pow_of_real {μ : Measure ℝ} {j : ℕ}
    (h : Integrable (fun x : ℝ => x ^ j) μ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ j) μ := by
  have hc : Integrable (fun x : ℝ => ((x ^ j : ℝ) : ℂ)) μ := h.ofReal
  simpa only [Complex.ofReal_pow] using hc

/-- Equality of ordinary real moments implies the complex moment equality
needed for complex analytic test functions. -/
theorem integral_complex_pow_eq_of_real {μ η : Measure ℝ} {j : ℕ}
    (h : (∫ x : ℝ, x ^ j ∂μ) = ∫ x : ℝ, x ^ j ∂η) :
    (∫ x : ℝ, (x : ℂ) ^ j ∂μ) = ∫ x : ℝ, (x : ℂ) ^ j ∂η := by
  simp_rw [← Complex.ofReal_pow, integral_complex_ofReal, h]

/-- Equal monomial moments give equal integrals of every complex polynomial
written as a finite coefficient sum. -/
theorem integral_polynomial_sum_eq_of_moments {μ η : Measure ℝ} {k : ℕ}
    (hμ : ∀ j ≤ k, Integrable (fun x : ℝ => (x : ℂ) ^ j) μ)
    (hη : ∀ j ≤ k, Integrable (fun x : ℝ => (x : ℂ) ^ j) η)
    (hm : ∀ j ≤ k, (∫ x : ℝ, (x : ℂ) ^ j ∂μ) = ∫ x : ℝ, (x : ℂ) ^ j ∂η)
    (a : ℕ → ℂ) :
    (∫ x : ℝ, ∑ j ∈ Finset.range (k + 1), a j * (x : ℂ) ^ j ∂μ) =
      ∫ x : ℝ, ∑ j ∈ Finset.range (k + 1), a j * (x : ℂ) ^ j ∂η := by
  rw [integral_finsetSum _ (fun j hj => (hμ j (by simpa using hj)).const_mul _),
    integral_finsetSum _ (fun j hj => (hη j (by simpa using hj)).const_mul _)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, integral_const_mul, hm j (by simpa using hj)]

/-- Binomial expansion converts shifted powers to ordinary moments. -/
theorem complex_shifted_pow_eq_sum (x : ℝ) (c : ℂ) (j : ℕ) :
    ((x : ℂ) - c) ^ j =
      ∑ l ∈ Finset.range (j + 1), ((-c) ^ (j - l) * (j.choose l : ℂ)) * (x : ℂ) ^ l := by
  rw [sub_eq_add_neg, add_pow]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Integrability of raw moments gives integrability of moments about any
complex center, by the finite binomial identity. -/
theorem integrable_shifted_pow_of_moments {μ : Measure ℝ} {k : ℕ}
    (hμ : ∀ j ≤ k, Integrable (fun x : ℝ => (x : ℂ) ^ j) μ)
    (c : ℂ) {j : ℕ} (hj : j ≤ k) :
    Integrable (fun x : ℝ => ((x : ℂ) - c) ^ j) μ := by
  simp_rw [complex_shifted_pow_eq_sum]
  apply integrable_finsetSum
  intro l hl
  exact (hμ l ((Nat.le_of_lt_succ (Finset.mem_range.mp hl)).trans hj)).const_mul _

/-- Equality of raw moments is invariant under a change of center. -/
theorem integral_shifted_pow_eq_of_moments {μ η : Measure ℝ} {k : ℕ}
    (hμ : ∀ j ≤ k, Integrable (fun x : ℝ => (x : ℂ) ^ j) μ)
    (hη : ∀ j ≤ k, Integrable (fun x : ℝ => (x : ℂ) ^ j) η)
    (hm : ∀ j ≤ k, (∫ x : ℝ, (x : ℂ) ^ j ∂μ) = ∫ x : ℝ, (x : ℂ) ^ j ∂η)
    (c : ℂ) {j : ℕ} (hj : j ≤ k) :
    (∫ x : ℝ, ((x : ℂ) - c) ^ j ∂μ) = ∫ x : ℝ, ((x : ℂ) - c) ^ j ∂η := by
  simp_rw [complex_shifted_pow_eq_sum]
  exact integral_polynomial_sum_eq_of_moments
    (fun l hl => hμ l (hl.trans hj)) (fun l hl => hη l (hl.trans hj))
    (fun l hl => hm l (hl.trans hj)) _

/-- Every Taylor polynomial of degree at most `k` integrates equally under
measures with equal raw moments through `k`. -/
theorem integral_shifted_polynomial_sum_eq_of_moments {μ η : Measure ℝ} {k : ℕ}
    (hμ : ∀ j ≤ k, Integrable (fun x : ℝ => (x : ℂ) ^ j) μ)
    (hη : ∀ j ≤ k, Integrable (fun x : ℝ => (x : ℂ) ^ j) η)
    (hm : ∀ j ≤ k, (∫ x : ℝ, (x : ℂ) ^ j ∂μ) = ∫ x : ℝ, (x : ℂ) ^ j ∂η)
    (c : ℂ) (a : ℕ → ℂ) :
    (∫ x : ℝ, ∑ j ∈ Finset.range (k + 1), a j * ((x : ℂ) - c) ^ j ∂μ) =
      ∫ x : ℝ, ∑ j ∈ Finset.range (k + 1), a j * ((x : ℂ) - c) ^ j ∂η := by
  rw [integral_finsetSum _ (fun j hj =>
      (integrable_shifted_pow_of_moments hμ c (by simpa using hj)).const_mul _),
    integral_finsetSum _ (fun j hj =>
      (integrable_shifted_pow_of_moments hη c (by simpa using hj)).const_mul _)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, integral_const_mul,
    integral_shifted_pow_eq_of_moments hμ hη hm c (by simpa using hj)]

/-- Integrating a uniformly controlled error against a difference of finite
positive measures costs at most the sum of their masses. The hypotheses prove
that all four displayed integrals have their ordinary, integrable meaning. -/
theorem norm_integral_sub_le_of_approximation {μ η : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure η] {F P : ℝ → ℂ} {ε : ℝ}
    (hFμ : Integrable F μ) (hFη : Integrable F η)
    (hPμ : Integrable P μ) (hPη : Integrable P η)
    (hP : (∫ x, P x ∂μ) = ∫ x, P x ∂η)
    (hεμ : ∀ᵐ x ∂μ, ‖F x - P x‖ ≤ ε)
    (hεη : ∀ᵐ x ∂η, ‖F x - P x‖ ≤ ε) :
    ‖(∫ x, F x ∂μ) - ∫ x, F x ∂η‖ ≤ (μ.real univ + η.real univ) * ε := by
  have heq : (∫ x, F x ∂μ) - (∫ x, F x ∂η) =
      (∫ x, F x - P x ∂μ) - (∫ x, F x - P x ∂η) := by
    rw [integral_sub hFμ hPμ, integral_sub hFη hPη, hP]
    ring
  rw [heq]
  calc
    _ ≤ ‖∫ x, F x - P x ∂μ‖ + ‖∫ x, F x - P x ∂η‖ := norm_sub_le _ _
    _ ≤ ε * μ.real univ + ε * η.real univ :=
      add_le_add (norm_integral_le_of_norm_le_const hεμ)
        (norm_integral_le_of_norm_le_const hεη)
    _ = (μ.real univ + η.real univ) * ε := by ring

/-- The finite-measure algebraic half of the Taylor cancellation estimate.
The function `a` can be the actual Taylor coefficient sequence; its remainder
bound is a hypothesis here, not an assumed analyticity theorem. -/
theorem norm_integral_sub_le_of_moment_approximation {μ η : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure η] {k : ℕ} {F : ℝ → ℂ} {ε : ℝ}
    (hμ : ∀ j ≤ k, Integrable (fun x : ℝ => (x : ℂ) ^ j) μ)
    (hη : ∀ j ≤ k, Integrable (fun x : ℝ => (x : ℂ) ^ j) η)
    (hm : ∀ j ≤ k, (∫ x : ℝ, (x : ℂ) ^ j ∂μ) = ∫ x : ℝ, (x : ℂ) ^ j ∂η)
    (hFμ : Integrable F μ) (hFη : Integrable F η) (c : ℂ) (a : ℕ → ℂ)
    (hεμ : ∀ᵐ x ∂μ, ‖F x - ∑ j ∈ Finset.range (k + 1),
      a j * ((x : ℂ) - c) ^ j‖ ≤ ε)
    (hεη : ∀ᵐ x ∂η, ‖F x - ∑ j ∈ Finset.range (k + 1),
      a j * ((x : ℂ) - c) ^ j‖ ≤ ε) :
    ‖(∫ x, F x ∂μ) - ∫ x, F x ∂η‖ ≤ (μ.real univ + η.real univ) * ε := by
  apply norm_integral_sub_le_of_approximation hFμ hFη
    (integrable_finsetSum _ fun j hj =>
      (integrable_shifted_pow_of_moments hμ c (by simpa using hj)).const_mul _)
    (integrable_finsetSum _ fun j hj =>
      (integrable_shifted_pow_of_moments hη c (by simpa using hj)).const_mul _)
    (integral_shifted_polynomial_sum_eq_of_moments hμ hη hm c a) hεμ hεη

end GapFamily.Analytic
