import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationUpper
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section
namespace GapFamily.Analytic
open Set UpperHalfPlane
open scoped ContDiff MatrixGroups

/-- A smooth denominator that agrees with P once Re P reaches one half,
and stays nonzero everywhere Re P is nonnegative. -/
def periodizationNormalizer (P : ℂ → ℂ) (z : ℂ) : ℂ :=
  P z + (Real.smoothTransition (1 - 2 * (P z).re) : ℂ)

theorem periodizationNormalizer_ne_zero {P : ℂ → ℂ} {z : ℂ}
    (hP : 0 ≤ (P z).re) : periodizationNormalizer P z ≠ 0 := by
  have hpos : 0 < (periodizationNormalizer P z).re := by
    change 0 < (P z).re + Real.smoothTransition (1 - 2 * (P z).re)
    by_cases hz : (P z).re = 0
    · simp [hz, Real.smoothTransition.one]
    · have hp : 0 < (P z).re := lt_of_le_of_ne hP (Ne.symm hz)
      linarith [Real.smoothTransition.nonneg (1 - 2 * (P z).re)]
  intro hz
  simp [hz] at hpos

theorem periodizationNormalizer_eq {P : ℂ → ℂ} {z : ℂ}
    (hP : (1 / 2 : ℝ) ≤ (P z).re) : periodizationNormalizer P z = P z := by
  have hh : 1 - 2 * (P z).re ≤ 0 := by linarith
  simp [periodizationNormalizer, Real.smoothTransition.zero_of_nonpos hh]

theorem contDiffOn_periodizationNormalizer {P : ℂ → ℂ} {U : Set ℂ}
    (hP : ContDiffOn ℝ ∞ P U) : ContDiffOn ℝ ∞ (periodizationNormalizer P) U := by
  have hr : ContDiffOn ℝ ∞ (fun z => (P z).re) U :=
    Complex.reCLM.contDiff.comp_contDiffOn hP
  have ht : ContDiffOn ℝ ∞ (fun z => Real.smoothTransition (1 - 2 * (P z).re)) U :=
    Real.smoothTransition.contDiff.comp_contDiffOn (contDiffOn_const.sub (contDiffOn_const.mul hr))
  exact hP.add (Complex.ofRealCLM.contDiff.comp_contDiffOn ht)

theorem periodizationNormalizer_invariant (φ : ℂ → ℂ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    periodizationNormalizer (modularPeriodization φ) (↑(γ • τ) : ℂ) =
      periodizationNormalizer (modularPeriodization φ) τ := by
  simp only [periodizationNormalizer, modularPeriodization_invariant]

end GapFamily.Analytic
