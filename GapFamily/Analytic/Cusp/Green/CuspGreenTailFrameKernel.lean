import GapFamily.Analytic.Cusp.Green.CuspGreenTailKernel
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Exact separation of the Robin frame Green tail

The observed frame is the ordinary position derivative plus one half of the
value. Its tail separates at every complex parameter, including the threshold.
-/

noncomputable section

namespace GapFamily.Analytic

/-- The observed Robin frame vector, with its removable threshold value. -/
def cuspGreenTailFrameValue (t : ℝ) (κ : ℂ) : ℂ :=
  Complex.cosh (κ * t) + (1 / 2 : ℂ) * cuspGreenTailValue t κ

@[simp] theorem cuspGreenTailFrameValue_zero (t : ℝ) :
    cuspGreenTailFrameValue t 0 = 1 + (t : ℂ) / 2 := by
  simp [cuspGreenTailFrameValue]
  ring

/-- The left Robin frame separates into source and observed factors. -/
theorem cuspGreenLeftSlope_add_half_eq_tailFrame (t u : ℝ) (htu : t ≤ u) (κ : ℂ) :
    cuspGreenLeftSlope 0 t u κ + (1 / 2 : ℂ) * cuspGreen 0 t u κ =
      Complex.exp (-κ * u) * cuspGreenTailFrameValue t κ := by
  rw [cuspGreenLeftSlope_eq_tail, cuspGreen_eq_tailValue t u htu κ]
  simp only [cuspGreenTailFrameValue, Complex.cosh, neg_mul]
  ring

/-- Source weighting shifts the Laplace parameter in the Robin frame tail. -/
theorem cuspGreenLeftSlope_add_half_mul_weight_eq_tailFrame (t u α : ℝ)
    (htu : t ≤ u) (κ : ℂ) :
    (cuspGreenLeftSlope 0 t u κ + (1 / 2 : ℂ) * cuspGreen 0 t u κ) *
        Complex.exp (-(α : ℂ) * u) =
      cuspGreenTailFrameValue t κ * Complex.exp (-((α : ℂ) + κ) * u) := by
  rw [cuspGreenLeftSlope_add_half_eq_tailFrame t u htu κ]
  have he : Complex.exp (-κ * u) * Complex.exp (-(α : ℂ) * u) =
      Complex.exp (-((α : ℂ) + κ) * u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = cuspGreenTailFrameValue t κ *
        (Complex.exp (-κ * u) * Complex.exp (-(α : ℂ) * u)) := by ring
    _ = _ := by rw [he]

/-- The same separation uses the actual derivative strictly below the source. -/
theorem cuspGreen_deriv_add_half_eq_tailFrame (t u : ℝ) (htu : t < u) (κ : ℂ) :
    deriv (fun v : ℝ => cuspGreen 0 v u κ) t +
        (1 / 2 : ℂ) * cuspGreen 0 t u κ =
      Complex.exp (-κ * u) * cuspGreenTailFrameValue t κ := by
  rw [(cuspGreen_hasDerivAt_left 0 t u htu κ).deriv]
  exact cuspGreenLeftSlope_add_half_eq_tailFrame t u htu.le κ

/-- The weighted identity also holds for the ordinary position derivative. -/
theorem cuspGreen_deriv_add_half_mul_weight_eq_tailFrame (t u α : ℝ)
    (htu : t < u) (κ : ℂ) :
    (deriv (fun v : ℝ => cuspGreen 0 v u κ) t +
        (1 / 2 : ℂ) * cuspGreen 0 t u κ) * Complex.exp (-(α : ℂ) * u) =
      cuspGreenTailFrameValue t κ * Complex.exp (-((α : ℂ) + κ) * u) := by
  rw [(cuspGreen_hasDerivAt_left 0 t u htu κ).deriv]
  exact cuspGreenLeftSlope_add_half_mul_weight_eq_tailFrame t u α htu.le κ

end GapFamily.Analytic
