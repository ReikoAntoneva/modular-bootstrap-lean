import GapFamily.Analytic.Cusp.Green.CuspGreenTailKernel
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorBasic
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorKernel

/-!
# The observed Green tail vector

The actual scalar tail value defines an entire vector in the uniform norm on
every finite observation collar, including at the threshold parameter.
-/

noncomputable section
namespace GapFamily.Analytic

/-- The genuine observed tail value, with the uniform norm on the collar. -/
def cuspGreenTailObserved (L : ℝ) (κ : ℂ) : C(CuspGreenCollar 0 L, ℂ) :=
  NormedSpace.exp
      (κ • (⟨fun t => ((t : ℝ) : ℂ), by fun_prop⟩ : C(CuspGreenCollar 0 L, ℂ))) *
    cuspGreenContinuousKernel 0
      ⟨Subtype.val, continuous_subtype_val⟩ ⟨Subtype.val, continuous_subtype_val⟩ κ

@[simp] theorem cuspGreenTailObserved_apply (L : ℝ) (κ : ℂ)
    (t : CuspGreenCollar 0 L) :
    cuspGreenTailObserved L κ t = cuspGreenTailValue (t : ℝ) κ := by
  simp [cuspGreenTailObserved, continuousKernel_exp_apply, cuspGreenTailValue]

/-- At threshold the observed vector is the actual coordinate function. -/
@[simp] theorem cuspGreenTailObserved_zero (L : ℝ) :
    cuspGreenTailObserved L 0 =
      (⟨fun t => ((t : ℝ) : ℂ), by fun_prop⟩ : C(CuspGreenCollar 0 L, ℂ)) := by
  ext t
  simp

/-- Entire dependence holds in the uniform norm, without deleting zero. -/
theorem differentiable_cuspGreenTailObserved (L : ℝ) :
    Differentiable ℂ (cuspGreenTailObserved L) :=
  (differentiable_exp_smul_const ℂ _).mul
    (differentiable_cuspGreenContinuousKernel 0 _ _)

theorem analyticAt_cuspGreenTailObserved (L : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenTailObserved L) κ :=
  (differentiable_cuspGreenTailObserved L).analyticAt κ

end GapFamily.Analytic
