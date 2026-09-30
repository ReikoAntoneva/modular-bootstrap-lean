import GapFamily.Analytic.Foundation.MomentIntegral
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Cancellation of a polynomial against a signed measure

All integrability hypotheses refer to the actual variation measure.  Polynomial
moment cancellation therefore controls the signed integral of an approximated
function by its uniform remainder times the total variation mass.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set
open scoped BigOperators

theorem signedMeasure_isFiniteMeasure_variation (ν : SignedMeasure ℝ) :
    IsFiniteMeasure ν.variation := by
  rw [← SignedMeasure.totalVariation_eq_variation]
  infer_instance

/-- The vector-measure integral agrees with the difference of the two genuine
Bochner integrals in the Jordan decomposition. -/
theorem signedIntegral_eq_jordan {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : SignedMeasure ℝ} {f : ℝ → E}
    (hf : ν.Integrable f) :
    (∫ᵛ x, f x ∂<•ν) =
      (∫ x, f x ∂ν.toJordanDecomposition.posPart) -
        ∫ x, f x ∂ν.toJordanDecomposition.negPart := by
  have hi : Integrable f
      (ν.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart) := by
    simpa only [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation,
      SignedMeasure.totalVariation] using hf
  have hp : ν.toJordanDecomposition.posPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
      using hi.left_of_add_measure
  have hn : ν.toJordanDecomposition.negPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
      using hi.right_of_add_measure
  conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure,
    VectorMeasure.integral_sub_vectorMeasure hp hn]
  simp only [VectorMeasure.integral_toSignedMeasure]

/-- Real signed integrals embed in the complex signed integral through the
actual Jordan decomposition. -/
theorem signedIntegral_complex_ofReal {ν : SignedMeasure ℝ} {f : ℝ → ℝ}
    (hf : ν.Integrable f) :
    (∫ᵛ x, (f x : ℂ) ∂<•ν) = Complex.ofReal (∫ᵛ x, f x ∂<•ν) := by
  rw [signedIntegral_eq_jordan hf.ofReal, signedIntegral_eq_jordan hf]
  simp only [integral_complex_ofReal, Complex.ofReal_sub]

theorem signedIntegrable_complex_pow_of_real {ν : SignedMeasure ℝ} {j : ℕ}
    (hi : ν.Integrable (fun x : ℝ => x ^ j)) :
    ν.Integrable (fun x : ℝ => (x : ℂ) ^ j) :=
  integrable_complex_pow_of_real hi

/-- The ordinary real signed moment condition supplies exactly the complex
moment condition needed by Taylor cancellation. -/
theorem signedIntegral_complex_pow_eq_of_real {ν : SignedMeasure ℝ} {j : ℕ}
    (hi : ν.Integrable (fun x : ℝ => x ^ j))
    (hm : (∫ᵛ x : ℝ, x ^ j ∂<•ν) = 0) :
    (∫ᵛ x : ℝ, (x : ℂ) ^ j ∂<•ν) = 0 := by
  simp only [← Complex.ofReal_pow, signedIntegral_complex_ofReal hi, hm,
    Complex.ofReal_zero]

theorem signedIntegral_const_mul {ν : SignedMeasure ℝ} {f : ℝ → ℂ}
    (hf : ν.Integrable f) (a : ℂ) :
    (∫ᵛ x, a * f x ∂<•ν) = a * ∫ᵛ x, f x ∂<•ν := by
  rw [signedIntegral_eq_jordan (hf.const_mul a), signedIntegral_eq_jordan hf,
    integral_const_mul, integral_const_mul, mul_sub]

/-- An actual finite complex polynomial in the coordinate integrates to zero
when all of its monomials do, with integrability required for every monomial. -/
theorem signedIntegral_sum_range_eq_zero {ν : SignedMeasure ℝ} {k : ℕ}
    (a : ℕ → ℂ)
    (hi : ∀ j ≤ k, ν.Integrable (fun x : ℝ => (x : ℂ) ^ j))
    (hm : ∀ j ≤ k, (∫ᵛ x : ℝ, (x : ℂ) ^ j ∂<•ν) = 0) :
    (∫ᵛ x : ℝ, ∑ j ∈ Finset.range (k + 1), a j * (x : ℂ) ^ j ∂<•ν) = 0 := by
  rw [VectorMeasure.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [signedIntegral_const_mul (hi j hjk), hm j hjk, mul_zero]
  · intro j hj
    exact (hi j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).const_mul (a j)

/-- Integrability of the finitely many coordinate monomials establishes genuine
integrability of every complex polynomial through the same degree. -/
theorem signedIntegrable_polynomial {ν : SignedMeasure ℝ} {k : ℕ}
    (p : Polynomial ℂ) (hk : p.natDegree ≤ k)
    (hi : ∀ j ≤ k, ν.Integrable (fun x : ℝ => (x : ℂ) ^ j)) :
    ν.Integrable (fun x : ℝ => p.eval (x : ℂ)) := by
  simp_rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hk)]
  apply VectorMeasure.Integrable.fun_finsetSum
  intro j hj
  exact (hi j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).const_mul (p.coeff j)

theorem signedIntegral_polynomial_eq_zero {ν : SignedMeasure ℝ} {k : ℕ}
    (p : Polynomial ℂ) (hk : p.natDegree ≤ k)
    (hi : ∀ j ≤ k, ν.Integrable (fun x : ℝ => (x : ℂ) ^ j))
    (hm : ∀ j ≤ k, (∫ᵛ x : ℝ, (x : ℂ) ^ j ∂<•ν) = 0) :
    (∫ᵛ x : ℝ, p.eval (x : ℂ) ∂<•ν) = 0 := by
  simpa only [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hk)] using
    signedIntegral_sum_range_eq_zero p.coeff hi hm

/-- Raw signed moment cancellation is invariant under changing the complex
center of the polynomial. -/
theorem signedIntegral_shifted_pow_eq_zero {ν : SignedMeasure ℝ} {k : ℕ}
    (hi : ∀ j ≤ k, ν.Integrable (fun x : ℝ => (x : ℂ) ^ j))
    (hm : ∀ j ≤ k, (∫ᵛ x : ℝ, (x : ℂ) ^ j ∂<•ν) = 0)
    (c : ℂ) {j : ℕ} (hj : j ≤ k) :
    (∫ᵛ x : ℝ, ((x : ℂ) - c) ^ j ∂<•ν) = 0 := by
  simp_rw [complex_shifted_pow_eq_sum]
  exact signedIntegral_sum_range_eq_zero _
    (fun l hl => hi l (hl.trans hj)) (fun l hl => hm l (hl.trans hj))

theorem signedIntegrable_shifted_sum {ν : SignedMeasure ℝ} {k : ℕ}
    (hi : ∀ j ≤ k, ν.Integrable (fun x : ℝ => (x : ℂ) ^ j))
    (c : ℂ) (a : ℕ → ℂ) :
    ν.Integrable (fun x : ℝ =>
      ∑ j ∈ Finset.range (k + 1), a j * ((x : ℂ) - c) ^ j) := by
  apply integrable_finsetSum
  intro j hj
  exact (integrable_shifted_pow_of_moments hi c
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).const_mul _

theorem signedIntegral_shifted_sum_eq_zero {ν : SignedMeasure ℝ} {k : ℕ}
    (hi : ∀ j ≤ k, ν.Integrable (fun x : ℝ => (x : ℂ) ^ j))
    (hm : ∀ j ≤ k, (∫ᵛ x : ℝ, (x : ℂ) ^ j ∂<•ν) = 0)
    (c : ℂ) (a : ℕ → ℂ) :
    (∫ᵛ x : ℝ, ∑ j ∈ Finset.range (k + 1), a j * ((x : ℂ) - c) ^ j ∂<•ν) = 0 := by
  rw [VectorMeasure.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [signedIntegral_const_mul (integrable_shifted_pow_of_moments hi c hjk),
      signedIntegral_shifted_pow_eq_zero hi hm c hjk, mul_zero]
  · intro j hj
    exact (integrable_shifted_pow_of_moments hi c
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).const_mul _

/-- Once the approximating polynomial has zero signed integral, only its
uniform remainder contributes.  Both integrals have explicit convergence. -/
theorem norm_signedIntegral_le_of_approximation {ν : SignedMeasure ℝ}
    {f p : ℝ → ℂ} {ε : ℝ} (hf : ν.Integrable f) (hp : ν.Integrable p)
    (hz : (∫ᵛ x, p x ∂<•ν) = 0)
    (he : ∀ᵐ x ∂ν.variation, ‖f x - p x‖ ≤ ε) :
    ‖∫ᵛ x, f x ∂<•ν‖ ≤ ν.variation.real univ * ε := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip) he
  rw [VectorMeasure.integral_fun_sub hf hp, hz, sub_zero] at h
  simpa only [ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.opNorm_lsmul,
    mul_one, mul_comm] using h

/-- Moment cancellation gives the total-variation remainder estimate for an
actual complex polynomial approximant. -/
theorem norm_signedIntegral_le_of_polynomial_approximation
    {ν : SignedMeasure ℝ} {k : ℕ} {f : ℝ → ℂ} {ε : ℝ}
    (p : Polynomial ℂ) (hk : p.natDegree ≤ k)
    (hi : ∀ j ≤ k, ν.Integrable (fun x : ℝ => (x : ℂ) ^ j))
    (hm : ∀ j ≤ k, (∫ᵛ x : ℝ, (x : ℂ) ^ j ∂<•ν) = 0)
    (hf : ν.Integrable f)
    (he : ∀ᵐ x ∂ν.variation, ‖f x - p.eval (x : ℂ)‖ ≤ ε) :
    ‖∫ᵛ x, f x ∂<•ν‖ ≤ ν.variation.real univ * ε :=
  norm_signedIntegral_le_of_approximation hf (signedIntegrable_polynomial p hk hi)
    (signedIntegral_polynomial_eq_zero p hk hi hm) he

/-- The same estimate in the Hahn–Jordan total-variation notation. -/
theorem norm_signedIntegral_le_totalVariation_of_polynomial_approximation
    {ν : SignedMeasure ℝ} {k : ℕ} {f : ℝ → ℂ} {ε : ℝ}
    (p : Polynomial ℂ) (hk : p.natDegree ≤ k)
    (hi : ∀ j ≤ k, ν.Integrable (fun x : ℝ => (x : ℂ) ^ j))
    (hm : ∀ j ≤ k, (∫ᵛ x : ℝ, (x : ℂ) ^ j ∂<•ν) = 0)
    (hf : ν.Integrable f)
    (he : ∀ᵐ x ∂ν.totalVariation, ‖f x - p.eval (x : ℂ)‖ ≤ ε) :
    ‖∫ᵛ x, f x ∂<•ν‖ ≤ ν.totalVariation.real univ * ε := by
  rw [SignedMeasure.totalVariation_eq_variation] at he ⊢
  exact norm_signedIntegral_le_of_polynomial_approximation p hk hi hm hf he

/-- The signed-measure Taylor cancellation estimate, expressed using actual
total variation and actual vector-measure integration. -/
theorem norm_signedIntegral_le_of_moment_approximation
    {ν : SignedMeasure ℝ} {k : ℕ} {f : ℝ → ℂ} {ε : ℝ}
    (hi : ∀ j ≤ k, ν.Integrable (fun x : ℝ => (x : ℂ) ^ j))
    (hm : ∀ j ≤ k, (∫ᵛ x : ℝ, (x : ℂ) ^ j ∂<•ν) = 0)
    (hf : ν.Integrable f) (c : ℂ) (a : ℕ → ℂ)
    (he : ∀ᵐ x ∂ν.totalVariation, ‖f x -
      ∑ j ∈ Finset.range (k + 1), a j * ((x : ℂ) - c) ^ j‖ ≤ ε) :
    ‖∫ᵛ x, f x ∂<•ν‖ ≤ ν.totalVariation.real univ * ε := by
  rw [SignedMeasure.totalVariation_eq_variation] at he ⊢
  exact norm_signedIntegral_le_of_approximation hf (signedIntegrable_shifted_sum hi c a)
    (signedIntegral_shifted_sum_eq_zero hi hm c a) he

end GapFamily.Analytic
