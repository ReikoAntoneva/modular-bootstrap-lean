import GapFamily.Analytic.Cusp.Green.CuspGreenTailFrameKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Ordinary integral of the observed Green tail vector

The primitive identity includes the removable parameter and uses the actual
finite-interval integral in the position variable.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory

/-- Away from threshold the entire observed vector has its usual quotient formula. -/
theorem cuspGreenTailValue_eq_sinh_div (t : ℝ) {κ : ℂ} (hκ : κ ≠ 0) :
    cuspGreenTailValue t κ = Complex.sinh (κ * t) / κ := by
  rw [cuspGreenTailValue, cuspGreen_eq_outgoing 0 t t hκ le_rfl]
  have he : Complex.exp (κ * t) * Complex.exp (-κ * t) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [← mul_assoc, he, one_mul]
  simp only [Complex.ofReal_zero, mul_zero, sub_zero, Complex.sinh, neg_mul]
  ring

/-- The denominator-free identity remains valid at threshold. -/
theorem cuspGreenTailValue_mul_sq (t : ℝ) (κ : ℂ) :
    κ ^ 2 * cuspGreenTailValue t κ = κ * Complex.sinh (κ * t) := by
  by_cases hκ : κ = 0
  · simp [hκ]
  · rw [cuspGreenTailValue_eq_sinh_div t hκ]
    field_simp

/-- Continuity in the observed position includes the threshold parameter. -/
theorem continuous_cuspGreenTailValue_position (κ : ℂ) :
    Continuous (fun t : ℝ => cuspGreenTailValue t κ) := by
  by_cases hκ : κ = 0
  · simp only [hκ, cuspGreenTailValue_zero]
    exact Complex.continuous_ofReal
  · simp_rw [cuspGreenTailValue_eq_sinh_div _ hκ]
    fun_prop

/-- The actual derivative of the hyperbolic cosine is the squared parameter times the tail vector. -/
theorem cuspGreenTail_cosh_hasDerivAt (t : ℝ) (κ : ℂ) :
    HasDerivAt (fun v : ℝ => Complex.cosh (κ * v))
      (κ ^ 2 * cuspGreenTailValue t κ) t := by
  rw [cuspGreenTailValue_mul_sq]
  simpa only [id_eq, mul_one, mul_comm] using
    (((hasDerivAt_id (t : ℂ)).const_mul κ).ccosh).comp_ofReal

/-- The actual finite-interval primitive reconstructs the derivative frame at every parameter. -/
theorem cuspGreenTailValue_integral_eq_cosh (t : ℝ) (κ : ℂ) :
    1 + κ ^ 2 * (∫ v : ℝ in 0..t, cuspGreenTailValue v κ) =
      Complex.cosh (κ * t) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t) (fun v _ => cuspGreenTail_cosh_hasDerivAt v κ)
    (((continuous_cuspGreenTailValue_position κ).const_mul (κ ^ 2)).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul] at h
  simpa only [Complex.ofReal_zero, mul_zero, Complex.cosh_zero, eq_sub_iff_add_eq,
    add_comm] using h

end GapFamily.Analytic
