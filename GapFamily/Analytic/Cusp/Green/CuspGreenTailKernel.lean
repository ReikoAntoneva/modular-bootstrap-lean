import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionDecay
import GapFamily.Analytic.Cusp.Green.CuspGreenODE

/-!
# Exact separation of the scalar Green tail

Below a source position the actual removable Green kernel separates into an
outgoing exponential in the source coordinate and an entire observed vector.
Both the value and the original logarithmic derivative identities include κ=0.
-/

noncomputable section
namespace GapFamily.Analytic

/-- The entire diagonal expression for the observed `sinh(κt)/κ` vector. -/
def cuspGreenTailValue (t : ℝ) (κ : ℂ) : ℂ :=
  Complex.exp (κ * t) * cuspGreen 0 t t κ

@[simp] theorem cuspGreenTailValue_zero (t : ℝ) :
    cuspGreenTailValue t 0 = (t : ℂ) := by
  simp [cuspGreenTailValue]

/-- Literal separation holds for every complex parameter, including threshold. -/
theorem cuspGreen_eq_tailValue (t u : ℝ) (htu : t ≤ u) (κ : ℂ) :
    cuspGreen 0 t u κ = Complex.exp (-κ * u) * cuspGreenTailValue t κ := by
  by_cases hκ : κ = 0
  · subst κ
    simp [min_eq_left htu]
  · rw [cuspGreen_symm, cuspGreen_eq_outgoing 0 u t hκ htu,
      cuspGreenTailValue, cuspGreen_eq_outgoing 0 t t hκ le_rfl]
    have he : Complex.exp (κ * t) * Complex.exp (-κ * t) = 1 := by
      rw [← Complex.exp_add]
      simp
    rw [← mul_assoc (Complex.exp (κ * t)), he, one_mul]

/-- The left derivative separates without a removable denominator. -/
theorem cuspGreenLeftSlope_eq_tail (t u : ℝ) (κ : ℂ) :
    cuspGreenLeftSlope 0 t u κ = Complex.exp (-κ * u) *
      ((Complex.exp (κ * t) + Complex.exp (-κ * t)) / 2) := by
  unfold cuspGreenLeftSlope
  push_cast
  rw [show -κ * ((u : ℂ) - t) = -κ * u + κ * t by ring,
    show -κ * ((t : ℂ) + u - 2 * 0) = -κ * u + -κ * t by ring,
    Complex.exp_add, Complex.exp_add]
  ring

/-- Multiplication by the true exponential source weight shifts the tail
Laplace parameter, without a restriction on the sign of κ. -/
theorem cuspGreen_mul_weight_eq_tail (t u α : ℝ) (htu : t ≤ u) (κ : ℂ) :
    cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) =
      cuspGreenTailValue t κ * Complex.exp (-((α : ℂ) + κ) * u) := by
  rw [cuspGreen_eq_tailValue t u htu κ]
  have he : Complex.exp (-κ * u) * Complex.exp (-(α : ℂ) * u) =
      Complex.exp (-((α : ℂ) + κ) * u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = cuspGreenTailValue t κ *
        (Complex.exp (-κ * u) * Complex.exp (-(α : ℂ) * u)) := by ring
    _ = _ := by rw [he]

end GapFamily.Analytic
