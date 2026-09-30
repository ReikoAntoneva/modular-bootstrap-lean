import GapFamily.Analytic.Cusp.Green.CuspGreenFrameSource
import GapFamily.Analytic.Cusp.Green.CuspGreenCompactResponse

/-!
# Entire bounded-height continuation of the actual scalar gradient

Only the already constructed physical gradient is clipped. No derivative of a
sharp cutoff, and no global form vector at threshold, is asserted.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient
open scoped Topology

/-- The continued vertical-frame output of the actual scalar Green response. -/
def cuspGreenFrameBoundedOutput (L T : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  (cuspGreenFrameSourceOperator L T κ).comp (cuspGreenSourceCoefficient T)

/-- The frame output is entire in the genuine bounded-operator norm. -/
theorem differentiable_cuspGreenFrameBoundedOutput (L T : ℝ) :
    Differentiable ℂ (cuspGreenFrameBoundedOutput L T) :=
  (differentiable_cuspGreenFrameSourceOperator L T).clm_comp
    (differentiable_const (cuspGreenSourceCoefficient T))

theorem analyticAt_cuspGreenFrameBoundedOutput (L T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenFrameBoundedOutput L T) κ :=
  (differentiable_cuspGreenFrameBoundedOutput L T).analyticAt κ

/-- Physical identification for every source supported below the source height. -/
theorem cuspGreenFrameBoundedOutput_eq_physical {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (F : ModularHilbert)
    (hF : modularHighCut (Real.exp T) F = 0) :
    cuspGreenFrameBoundedOutput L T κ F = modularLowCut (Real.exp L)
      (cuspScalarGradient (cuspScalarPencilSolution (1 / 4 - κ ^ 2) F)).ofLp.2 := by
  rw [cuspScalarPencilSolution_eq_greenCoefficient hT hκ F hF]
  exact cuspGreenFrameSourceOperator_eq_physical hL hT hκ (cuspGreenSourceCoefficient T F)

/-- The input and the original physical gradient output are both restricted to finite heights. -/
def cuspGreenFrameLocalizedOutput (L T : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  (cuspGreenFrameBoundedOutput L T κ).comp (modularLowCut (Real.exp T))

theorem differentiable_cuspGreenFrameLocalizedOutput (L T : ℝ) :
    Differentiable ℂ (cuspGreenFrameLocalizedOutput L T) :=
  (differentiable_cuspGreenFrameBoundedOutput L T).clm_comp
    (differentiable_const (modularLowCut (Real.exp T)))

theorem analyticAt_cuspGreenFrameLocalizedOutput (L T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenFrameLocalizedOutput L T) κ :=
  (differentiable_cuspGreenFrameLocalizedOutput L T).analyticAt κ

/-- In the physical half-plane the entire map is exactly the clipped actual closed gradient. -/
theorem cuspGreenFrameLocalizedOutput_eq_physical {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) :
    cuspGreenFrameLocalizedOutput L T κ =
      ((modularLowCut (Real.exp L)).comp
        (((WithLp.sndL 2 ℂ ModularHilbert ModularHilbert).comp cuspScalarGradient).comp
          (cuspScalarPencilSolution (1 / 4 - κ ^ 2)))).comp
            (modularLowCut (Real.exp T)) := by
  apply ContinuousLinearMap.ext
  intro F
  exact cuspGreenFrameBoundedOutput_eq_physical hL hT hκ
    (modularLowCut (Real.exp T) F) (modularHighCut_lowCut (Real.exp T) F)

/-- The threshold limit is an operator-norm limit of local gradient outputs. -/
theorem cuspGreenFrameLocalizedOutput_tendsto_zero (L T : ℝ) :
    Tendsto (cuspGreenFrameLocalizedOutput L T) (𝓝 (0 : ℂ))
      (𝓝 (cuspGreenFrameLocalizedOutput L T 0)) :=
  (differentiable_cuspGreenFrameLocalizedOutput L T).continuous.tendsto 0

end GapFamily.Analytic
