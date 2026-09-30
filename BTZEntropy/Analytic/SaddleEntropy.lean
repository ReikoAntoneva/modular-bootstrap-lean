import BTZEntropy.Analytic.LogExpansion
import BTZEntropy.Analytic.Prefactor

/-! Uniform transfer from normalized count expansions to entropy bounds
at every sufficiently large real central charge. -/

noncomputable section

open Set Filter
open scoped BigOperators

namespace BTZEntropy

/-- A real-charge count expansion with the specified Gaussian scale and
finite Taylor--Gaussian coefficients, uniformly on compact positive ratios. -/
def UniformSaddleCountExpansion (φ : SmoothKernel) (reference : ℝ → ℝ → ℝ) : Prop :=
  ∀ (P : ℕ) (L U : ℝ), 0 < L → L ≤ U →
    ∃ D > 0, ∃ c₀ ≥ (1 : ℝ), ∀ c, c₀ ≤ c → ∀ x ∈ Icc L U,
      |reference x c / saddleCountScale φ x c -
          (1 + (countCorrectionPolynomial φ x P).eval c⁻¹)| ≤ D / c ^ (P + 1)

/-- Charge lower bounds replace all radius and small-error conditions in
the finite logarithm theorem by explicit inequalities. -/
theorem saddle_count_pos_and_normalized_log_error
    (φ : SmoothKernel) {x c N M D : ℝ} (P : ℕ)
    (hx : 0 < x) (hc : 1 ≤ c) (hM : 0 ≤ M)
    (hu : ∀ n, 1 ≤ n → n ≤ P → |saddleCountCoefficient φ x n| ≤ M)
    (hcM : 2 * (P * M) ≤ c) (hcD : 4 * D ≤ c)
    (herr : |N / saddleCountScale φ x c -
      (1 + (countCorrectionPolynomial φ x P).eval c⁻¹)| ≤ D / c ^ (P + 1)) :
    0 < N ∧
      |Real.log (N / saddleCountScale φ x c) -
        ∑ j ∈ Finset.range P, entropyCoefficient φ x (j + 1) * c⁻¹ ^ (j + 1)| ≤
      (4 * D + 2 * (P * M) ^ (P + 1) + logarithmPolynomialCoeffBound P M) /
        c ^ (P + 1) := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hε : 0 ≤ c⁻¹ := (inv_pos.mpr hcpos).le
  have hε1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  have hsmall : (P * M) * c⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hcpos).2
    linarith
  have hpow : c ≤ c ^ (P + 1) := le_self_pow₀ hc (by omega)
  have hDsmall : D * c⁻¹ ^ (P + 1) ≤ 1 / 4 := by
    rw [inv_pow, ← div_eq_mul_inv]
    apply (div_le_iff₀ (pow_pos hcpos _)).2
    linarith
  have herr' : |N / saddleCountScale φ x c -
      (1 + (countCorrectionPolynomial φ x P).eval c⁻¹)| ≤ D * c⁻¹ ^ (P + 1) := by
    simpa only [inv_pow, div_eq_mul_inv] using herr
  have h := pos_and_abs_log_count_sub_entropy_uniform_le φ x P hM hε hε1 hu
    hsmall herr' hDsmall
  refine ⟨(div_pos_iff_of_pos_right (saddleCountScale_pos φ hx hcpos)).mp h.1, ?_⟩
  simpa only [inv_pow, div_eq_mul_inv] using h.2

end BTZEntropy
