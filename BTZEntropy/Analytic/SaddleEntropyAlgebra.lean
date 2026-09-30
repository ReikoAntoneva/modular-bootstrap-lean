import BTZEntropy.Analytic.Prefactor
import BTZEntropy.Contract

/-! Exact identities relating the saddle count scale to the prescribed entropy
truncation, including order zero. -/

noncomputable section

open scoped BigOperators

namespace BTZEntropy

/-- The Gaussian count scale supplies exactly the leading action, logarithmic
term and constant coefficient of the prescribed entropy truncation. -/
theorem entropyTruncation_eq_log_saddleCountScale_add
    (φ : SmoothKernel) {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (P : ℕ) :
    entropyTruncation φ x c P = Real.log (saddleCountScale φ x c) +
      ∑ j ∈ Finset.range P, entropyCoefficient φ x (j + 1) * (c⁻¹) ^ (j + 1) := by
  rw [entropyTruncation, Finset.sum_range_succ', log_saddleCountScale φ hx hc]
  simp only [entropyCoefficient_zero, pow_zero, div_eq_mul_inv, inv_pow]
  ring

/-- A positive count has precisely the entropy error of its normalized ratio,
after subtracting the designated higher-order correction polynomial. -/
theorem log_sub_entropyTruncation_eq_log_ratio_sub
    (φ : SmoothKernel) {x c N : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hN : 0 < N) (P : ℕ) :
    Real.log N - entropyTruncation φ x c P =
      Real.log (N / saddleCountScale φ x c) -
        ∑ j ∈ Finset.range P, entropyCoefficient φ x (j + 1) * (c⁻¹) ^ (j + 1) := by
  rw [entropyTruncation_eq_log_saddleCountScale_add φ hx hc P,
    Real.log_div hN.ne' (saddleCountScale_pos φ hx hc).ne']
  ring

end BTZEntropy
