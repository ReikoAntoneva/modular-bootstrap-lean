import GapFamily.Analytic.Transform.FiniteLaplaceDensity
import GapFamily.Analytic.Transform.LaplaceKernelPairing

/-! Exact ordinary identity pairings for arbitrary complex finite Laplace rows. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Filter

/-- The conjugate pairing of two actual finite Laplace rows expands into their
literal real basis products, with arbitrary complex coefficients. -/
theorem star_finiteLaplaceSum_mul {m n : ℕ} (c : Fin m → ℂ) (d : Fin n → ℂ) (E : ℝ) :
    star (finiteLaplaceSum c E) * finiteLaplaceSum d E =
      ∑ k, ∑ l, star (c k) *
        ((laplaceTest k.val E * laplaceTest l.val E : ℝ) : ℂ) * d l := by
  simp only [finiteLaplaceSum, star_sum, star_mul, Complex.star_def,
    Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum, Complex.ofReal_mul]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem integrable_finiteLaplaceIdentityTerm (j : ℤ) {m n : ℕ}
    (c : Fin m → ℂ) (d : Fin n → ℂ) (k : Fin m) (l : Fin n) :
    Integrable (fun E => star (c k) *
      ((laplaceTest k.val E * laplaceTest l.val E : ℝ) : ℂ) * d l) (referenceMeasure j) :=
  ((integrable_laplaceTest_product_referenceMeasure j k.val l.val).ofReal.const_mul
    (star (c k))).mul_const (d l)

/-- The finite conjugate pairing is ordinarily absolutely integrable, including
the scalar endpoint. All pairwise convergence is already proved for the basis. -/
theorem integrable_star_finiteLaplaceSum_mul (j : ℤ) {m n : ℕ}
    (c : Fin m → ℂ) (d : Fin n → ℂ) :
    Integrable (fun E => star (finiteLaplaceSum c E) * finiteLaplaceSum d E)
      (referenceMeasure j) := by
  apply (integrable_finsetSum Finset.univ (fun k _ =>
    integrable_finsetSum Finset.univ (fun l _ =>
      integrable_finiteLaplaceIdentityTerm j c d k l))).congr
  exact Eventually.of_forall fun E => (star_finiteLaplaceSum_mul c d E).symm

/-- Ordinary complex integration commutes with both finite coefficient sums. -/
theorem integral_star_finiteLaplaceSum_mul (j : ℤ) {m n : ℕ}
    (c : Fin m → ℂ) (d : Fin n → ℂ) :
    (∫ E, star (finiteLaplaceSum c E) * finiteLaplaceSum d E ∂referenceMeasure j) =
      ∑ k, ∑ l, star (c k) *
        ((∫ E, laplaceTest k.val E * laplaceTest l.val E ∂referenceMeasure j) : ℂ) * d l := by
  simp_rw [star_finiteLaplaceSum_mul c d]
  rw [integral_finsetSum Finset.univ (fun k _ =>
    integrable_finsetSum Finset.univ (fun l _ =>
      integrable_finiteLaplaceIdentityTerm j c d k l))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum Finset.univ (fun l _ =>
    integrable_finiteLaplaceIdentityTerm j c d k l)]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_mul_const, integral_const_mul]
  simp only [Complex.ofReal_mul]

/-- The identity quadratic form of every finite Laplace row is an ordinary
integrable squared norm for every spin, including spin zero. -/
theorem integrable_norm_sq_finiteLaplaceSum_referenceMeasure (j : ℤ) {n : ℕ}
    (c : Fin n → ℂ) :
    Integrable (fun E => ‖finiteLaplaceSum c E‖ ^ 2) (referenceMeasure j) := by
  simpa only [RCLike.star_def, RCLike.conj_mul, RCLike.re_ofReal_pow] using
    (integrable_star_finiteLaplaceSum_mul j c c).re

/-- Exact finite Gram expansion of the real identity quadratic term. -/
theorem integral_norm_sq_finiteLaplaceSum_referenceMeasure (j : ℤ) {n : ℕ}
    (c : Fin n → ℂ) :
    (∫ E, ‖finiteLaplaceSum c E‖ ^ 2 ∂referenceMeasure j) =
      (∑ k, ∑ l, star (c k) *
        ((∫ E, laplaceTest k.val E * laplaceTest l.val E ∂referenceMeasure j) : ℂ) * c l).re := by
  calc
    _ = (∫ E, star (finiteLaplaceSum c E) * finiteLaplaceSum c E ∂referenceMeasure j).re := by
      simpa only [RCLike.star_def, RCLike.conj_mul, RCLike.re_ofReal_pow,
        RCLike.re_eq_complex_re] using
        integral_re (integrable_star_finiteLaplaceSum_mul j c c)
    _ = _ := congrArg Complex.re (integral_star_finiteLaplaceSum_mul j c c)

end GapFamily.Analytic
