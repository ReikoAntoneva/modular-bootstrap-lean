import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorBasic
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorKernel
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorLinear

/-! Entire operator-norm dependence of the actual finite-collar Green family. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Filter Set
open scoped Topology

/-- The actual collar kernel is entire in its uniform spatial norm. -/
theorem differentiable_cuspGreenCollarKernel (t₀ T : ℝ) :
    Differentiable ℂ (cuspGreenCollarKernel t₀ T) := by
  let t : C(CuspGreenCollar t₀ T × CuspGreenCollar t₀ T, ℝ) :=
    ⟨fun p => p.1, continuous_subtype_val.comp continuous_fst⟩
  let u : C(CuspGreenCollar t₀ T × CuspGreenCollar t₀ T, ℝ) :=
    ⟨fun p => p.2, continuous_subtype_val.comp continuous_snd⟩
  have heq : cuspGreenCollarKernel t₀ T = cuspGreenContinuousKernel t₀ t u := by
    funext κ
    ext p
    rfl
  rw [heq]
  exact differentiable_cuspGreenContinuousKernel t₀ t u

/-- The bounded Green map into continuous functions is entire in operator norm. -/
theorem differentiable_cuspGreenCollarOperator (t₀ T : ℝ) :
    Differentiable ℂ (cuspGreenCollarOperator t₀ T) := by
  let M : C(CuspGreenCollar t₀ T × CuspGreenCollar t₀ T, ℂ) →L[ℂ]
      (Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) →L[ℂ] C(CuspGreenCollar t₀ T, ℂ)) :=
    compactKernelOperatorMap (cuspGreenCollarMeasure t₀ T)
  have h := Differentiable.comp
    (G := Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) →L[ℂ] C(CuspGreenCollar t₀ T, ℂ))
    (ContinuousLinearMap.differentiable
      (F := Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) →L[ℂ] C(CuspGreenCollar t₀ T, ℂ)) M)
    (differentiable_cuspGreenCollarKernel t₀ T)
  convert! h using 1

/-- Entire continuation of the actual L² operator through the threshold. -/
theorem differentiable_cuspGreenCollarL2Operator (t₀ T : ℝ) :
    Differentiable ℂ (cuspGreenCollarL2Operator t₀ T) := by
  have h := (compactKernelL2OperatorMap (cuspGreenCollarMeasure t₀ T)
    (cuspGreenCollarMeasure t₀ T)).differentiable.comp
      (differentiable_cuspGreenCollarKernel t₀ T)
  convert! h using 1

/-- Holomorphy concerns the normed space of actual continuous linear operators. -/
theorem analyticAt_cuspGreenCollarOperator (t₀ T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenCollarOperator t₀ T) κ :=
  (differentiable_cuspGreenCollarOperator t₀ T).analyticAt κ

theorem analyticAt_cuspGreenCollarL2Operator (t₀ T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenCollarL2Operator t₀ T) κ :=
  (differentiable_cuspGreenCollarL2Operator t₀ T).analyticAt κ

/-- The threshold limit is in operator norm, with its actual min-kernel value. -/
theorem cuspGreenCollarL2Operator_tendsto_zero (t₀ T : ℝ) :
    Tendsto (cuspGreenCollarL2Operator t₀ T) (𝓝 (0 : ℂ))
      (𝓝 (cuspGreenCollarL2Operator t₀ T 0)) :=
  (differentiable_cuspGreenCollarL2Operator t₀ T).continuous.tendsto 0

/-- The actual threshold operator remains an ordinary, integrable min-kernel response. -/
theorem cuspGreenCollarOperator_zero_apply (t₀ T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) (t : CuspGreenCollar t₀ T) :
    cuspGreenCollarOperator t₀ T 0 f t =
      ∫ u : CuspGreenCollar t₀ T, ((min (t : ℝ) (u : ℝ) - t₀ : ℝ) : ℂ) * f u
        ∂cuspGreenCollarMeasure t₀ T := by
  simp only [cuspGreenCollarOperator_apply, cuspGreen_zero]

end GapFamily.Analytic
