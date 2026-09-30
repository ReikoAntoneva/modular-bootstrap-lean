import GapFamily.Analytic.Cusp.Green.CuspGreenTailObserved
import GapFamily.Analytic.Cusp.Green.CuspGreenTailFrameKernel

/-!
# The observed vertical-frame tail vector

The shifted first derivative of the actual Green tail is an entire vector in
the uniform norm on a finite observation collar. The formula retains the
threshold parameter and its nonzero boundary value.
-/

noncomputable section
namespace GapFamily.Analytic

/-- The literal observed shifted derivative, expressed in the continuous-function
Banach algebra so that parameter regularity is in its uniform norm. -/
def cuspGreenTailFrameObserved (L : ℝ) (κ : ℂ) : C(CuspGreenCollar 0 L, ℂ) :=
  (1 / 2 : ℂ) •
    (NormedSpace.exp
      (κ • (⟨fun t => ((t : ℝ) : ℂ), by fun_prop⟩ : C(CuspGreenCollar 0 L, ℂ))) +
    NormedSpace.exp
      ((-κ) • (⟨fun t => ((t : ℝ) : ℂ), by fun_prop⟩ : C(CuspGreenCollar 0 L, ℂ)))) +
  (1 / 2 : ℂ) • cuspGreenTailObserved L κ

@[simp] theorem cuspGreenTailFrameObserved_apply (L : ℝ) (κ : ℂ)
    (t : CuspGreenCollar 0 L) :
    cuspGreenTailFrameObserved L κ t = cuspGreenTailFrameValue (t : ℝ) κ := by
  simp [cuspGreenTailFrameObserved, continuousKernel_exp_apply,
    cuspGreenTailFrameValue, Complex.cosh]
  ring

/-- At threshold the shifted derivative is `1+t/2`. -/
@[simp] theorem cuspGreenTailFrameObserved_zero (L : ℝ) :
    cuspGreenTailFrameObserved L 0 =
      (⟨fun t => 1 + ((t : ℝ) : ℂ) / 2, by fun_prop⟩ : C(CuspGreenCollar 0 L, ℂ)) := by
  ext t
  simp

/-- Entire dependence is in the observed uniform norm, including zero. -/
theorem differentiable_cuspGreenTailFrameObserved (L : ℝ) :
    Differentiable ℂ (cuspGreenTailFrameObserved L) := by
  have hp := differentiable_exp_smul_const ℂ
    (⟨fun t => ((t : ℝ) : ℂ), by fun_prop⟩ : C(CuspGreenCollar 0 L, ℂ))
  have hn := hp.comp differentiable_neg
  exact ((hp.add hn).const_smul (1 / 2 : ℂ)).add
    ((differentiable_cuspGreenTailObserved L).const_smul (1 / 2 : ℂ))

theorem analyticAt_cuspGreenTailFrameObserved (L : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenTailFrameObserved L) κ :=
  (differentiable_cuspGreenTailFrameObserved L).analyticAt κ

end GapFamily.Analytic
