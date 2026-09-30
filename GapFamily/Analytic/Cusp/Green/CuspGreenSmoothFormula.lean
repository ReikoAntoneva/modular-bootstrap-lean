import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionFormula
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smoothness of the actual finite-integral cusp Green response

The established derivative certificates form a first-order system for the
response and its derivative. Simultaneous induction upgrades them to every
finite order for a smooth source. No smoothness of arbitrary L² sources is assumed.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped ContDiff

private theorem contDiff_cuspGreenSolutionFormula_pair_nat
    (a T : ℝ) {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ n (cuspGreenSolutionFormula a T κ f) ∧
      ContDiff ℝ n (cuspGreenSolutionFormulaDeriv a T κ f) := by
  have hV : Differentiable ℝ (cuspGreenSolutionFormula a T κ f) :=
    fun t => (hasDerivAt_cuspGreenSolutionFormula a T hκ hf.continuous t).differentiableAt
  have hD : Differentiable ℝ (cuspGreenSolutionFormulaDeriv a T κ f) :=
    fun t => (hasDerivAt_cuspGreenSolutionFormulaDeriv a T hf.continuous t).differentiableAt
  have hVD : deriv (cuspGreenSolutionFormula a T κ f) =
      cuspGreenSolutionFormulaDeriv a T κ f :=
    funext (deriv_cuspGreenSolutionFormula a T hκ hf.continuous)
  have hDD : deriv (cuspGreenSolutionFormulaDeriv a T κ f) =
      fun t => κ ^ 2 * cuspGreenSolutionFormula a T κ f t - f t :=
    funext fun t => (hasDerivAt_cuspGreenSolutionFormulaDeriv a T hf.continuous t).deriv
  induction n with
  | zero =>
      exact ⟨contDiff_zero.mpr hV.continuous, contDiff_zero.mpr hD.continuous⟩
  | succ n ih =>
      have hfn : ContDiff ℝ n f := hf.of_le (by simp)
      constructor
      · have hderiv : ContDiff ℝ n (deriv (cuspGreenSolutionFormula a T κ f)) := by
          rw [hVD]
          exact ih.2
        simpa only [Nat.cast_add, Nat.cast_one] using
          contDiff_succ_iff_deriv.mpr ⟨hV, by simp, hderiv⟩
      · have hderiv : ContDiff ℝ n (deriv (cuspGreenSolutionFormulaDeriv a T κ f)) := by
          rw [hDD]
          exact (contDiff_const.mul ih.1).sub hfn
        simpa only [Nat.cast_add, Nat.cast_one] using
          contDiff_succ_iff_deriv.mpr ⟨hD, by simp, hderiv⟩

/-- Smooth sources give a genuinely smooth finite-integral Green response. -/
theorem contDiff_cuspGreenSolutionFormula
    (a T : ℝ) {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cuspGreenSolutionFormula a T κ f) :=
  contDiff_infty.mpr fun n => (contDiff_cuspGreenSolutionFormula_pair_nat a T hκ hf n).1

/-- The explicitly differentiated response is smooth to every order as well. -/
theorem contDiff_cuspGreenSolutionFormulaDeriv
    (a T : ℝ) {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cuspGreenSolutionFormulaDeriv a T κ f) :=
  contDiff_infty.mpr fun n => (contDiff_cuspGreenSolutionFormula_pair_nat a T hκ hf n).2

/-- The finite-integral formula itself has zero Dirichlet value at its lower endpoint. -/
theorem cuspGreenSolutionFormula_boundary (a T : ℝ) (κ : ℂ) (f : ℝ → ℂ) :
    cuspGreenSolutionFormula a T κ f a = 0 := by
  unfold cuspGreenSolutionFormula
  rw [intervalIntegral.integral_same, mul_zero, zero_add]
  rw [show -κ * ((a : ℂ) - 2 * (a : ℂ)) = κ * (a : ℂ) by ring,
    sub_self, zero_div]


end GapFamily.Analytic
