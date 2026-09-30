import BTZEntropy.Analytic.SaddleJetIntegral
import BTZEntropy.Analytic.SaddlePolynomialIntegral
import BTZEntropy.Analytic.SaddleCount
import BTZEntropy.Analytic.IntegralTaylor

/-! The actual integrated Taylor polynomial has the designated BTZ coefficients. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BTZEntropy

theorem integralTaylorPolynomial_rescaledSaddleIntegrand (φ : SmoothKernel)
    {x : ℝ} (hx : 0 < x) (P : ℕ) (ε : ℝ) :
    Analytic.integralTaylorPolynomial volume
      (fun ε t : ℝ => rescaledSaddleIntegrand (complexAmplitude φ)
        (saddleBeta x) t (ε : ℂ)) (2 * P + 1) ε =
      (gaussianCountNormalization φ x *
        (1 + (countCorrectionPolynomial φ x P).eval (ε ^ 2)) : ℝ) := by
  unfold Analytic.integralTaylorPolynomial
  simp only [Complex.real_smul]
  calc
    _ = (Real.sqrt (2 * Real.pi / saddleHessian x) : ℂ) *
        ((∑ n ∈ Finset.range (2 * P + 2), ε ^ n * gaussianEvaluation (saddleHessian x)
          ((amplitudeTaylor φ x (2 * P + 1) * phaseExponential x (2 * P + 1)).coeff n)) : ℝ) := by
      rw [Complex.ofReal_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnN : n ≤ 2 * P + 1 := by simpa using Finset.mem_range.mp hn
      rw [integral_rescaledSaddleIntegrand_real_jet φ hx (2 * P + 1) hnN]
      push_cast
      have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp
    _ = _ := by
      rw [gaussian_saddlePolynomial_sum φ x ε P (amplitude_ne_zero φ (saddleBeta_pos hx)),
        gaussianCountNormalization_eq φ hx]
      push_cast
      ring

end BTZEntropy
