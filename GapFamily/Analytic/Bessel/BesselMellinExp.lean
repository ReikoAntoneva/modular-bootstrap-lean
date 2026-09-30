import GapFamily.Analytic.Bessel.BesselCoshOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
namespace GapFamily.Analytic.BesselCoshOrder
open MeasureTheory Set

/-- Exact logarithmic change of variables for the symmetric Mellin kernel. -/
theorem mellin_exp_substitution (κ : ℂ) (c u : ℝ) :
    Real.exp u • ((Real.exp u : ℂ) ^ (κ - 1) *
      Complex.exp (-(c : ℂ) * (Real.exp u : ℂ) - (c : ℂ) / (Real.exp u : ℂ))) =
    Complex.exp (-((2 * c : ℝ) : ℂ) * (Real.cosh u : ℂ)) *
      Complex.exp (κ * (u : ℂ)) := by
  have hn : (Real.exp u : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero u
  rw [Complex.real_smul, Complex.cpow_sub _ _ hn, Complex.cpow_one]
  have hp : (Real.exp u : ℂ) ^ κ = Complex.exp ((u : ℂ) * κ) := by
    rw [Complex.cpow_def_of_ne_zero hn]
    congr 1
    rw [← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  rw [hp]
  have he : -(c : ℂ) * (Real.exp u : ℂ) - (c : ℂ) / (Real.exp u : ℂ) =
      -((2 * c : ℝ) : ℂ) * (Real.cosh u : ℂ) := by
    rw [Real.cosh_eq, Real.exp_neg]
    push_cast
    ring
  rw [he]
  rw [mul_comm (u : ℂ) κ]
  field_simp

end GapFamily.Analytic.BesselCoshOrder
