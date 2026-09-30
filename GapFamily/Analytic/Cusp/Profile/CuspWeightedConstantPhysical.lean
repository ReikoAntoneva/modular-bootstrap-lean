import GapFamily.Analytic.Cusp.Profile.CuspWeightedConstantPairing
import GapFamily.Analytic.Cusp.Profile.CuspHalfLineWeightedInput

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory

/-- The continued weighted constant observation agrees with the actual scalar
resolvent for every ambient Hilbert source on the physical half-plane near threshold. -/
theorem cuspWeightedConstantPairingFunctional_eq_physical {α : ℝ} (hα : 0 ≤ α)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) (F : ModularHilbert) :
    cuspWeightedConstantPairingFunctional α κ F =
      inner ℂ modularConstant (scalarCuspEmbedding
        (cuspScalarPencilSolution ((1 / 4 : ℂ) - κ ^ 2) (cuspWeightedInput α hα F))) := by
  have hβ : 0 < ((α : ℂ) + κ).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hm : κ ≠ -(1 / 2 : ℂ) := by intro h; subst κ; norm_num at hκ
  rw [cuspScalarPencilSolution_constant_halfLinePairing hκ,
    cuspWeightedConstantPairingFunctional_apply hα hβ hp hm,
    cuspHalfLineSourceCoefficient_weightedInput]
  apply integral_congr_ae
  filter_upwards [cuspHalfLineWeight_ae α hα (cuspHalfLineSourceCoefficient F)] with t ht
  rw [ht]
  simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

end GapFamily.Analytic
