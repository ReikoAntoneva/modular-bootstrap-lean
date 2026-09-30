import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorTrace
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorKernel
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorLinear

/-! Entire operator-norm dependence of the actual finite-collar boundary trace. -/

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Filter Set
open scoped Topology

/-- The genuine exponential trace kernel is entire in its uniform spatial norm. -/
theorem differentiable_cuspGreenCollarTraceKernel (t₀ T : ℝ) :
    Differentiable ℂ (cuspGreenCollarTraceKernel t₀ T) := by
  let v : C(CuspGreenCollar t₀ T, ℂ) :=
    ⟨fun u => -((((u : ℝ) - t₀ : ℝ) : ℂ)), by fun_prop⟩
  have heq : cuspGreenCollarTraceKernel t₀ T =
      (fun κ : ℂ => NormedSpace.exp (κ • v)) := by
    funext κ
    ext u
    simp only [cuspGreenCollarTraceKernel, continuousKernel_exp_apply,
      ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.coe_mk, v]
    congr 1
    ring
  rw [heq]
  exact differentiable_exp_smul_const ℂ v

/-- The proved boundary functional is entire as an operator on the actual source `L²` space. -/
theorem differentiable_cuspGreenCollarTraceOperator (t₀ T : ℝ) :
    Differentiable ℂ (cuspGreenCollarTraceOperator t₀ T) := by
  let p : C(Unit × CuspGreenCollar t₀ T, CuspGreenCollar t₀ T) :=
    ⟨Prod.snd, continuous_snd⟩
  let M : C(CuspGreenCollar t₀ T, ℂ) →L[ℂ]
      (Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) →L[ℂ] ℂ) :=
    ((ContinuousLinearMap.compL ℂ (Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) C(Unit, ℂ) ℂ
      (ContinuousMap.evalCLM ℂ ())).comp
        (compactKernelOperatorMap (cuspGreenCollarMeasure t₀ T))).comp
          (ContinuousMap.compCLM ℂ ℂ p)
  have heq : cuspGreenCollarTraceOperator t₀ T =
      (fun κ : ℂ => M (cuspGreenCollarTraceKernel t₀ T κ)) := by
    funext κ
    ext f
    rw [cuspGreenCollarTraceOperator_apply]
    change _ = compactKernelIntegralOperator (cuspGreenCollarMeasure t₀ T)
      ((cuspGreenCollarTraceKernel t₀ T κ).comp p) f ()
    rw [compactKernelIntegralOperator_apply]
    rfl
  rw [heq]
  exact Differentiable.comp
    (G := Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) →L[ℂ] ℂ)
    (ContinuousLinearMap.differentiable
      (F := Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) →L[ℂ] ℂ) M)
    (differentiable_cuspGreenCollarTraceKernel t₀ T)

/-- The trace is holomorphic in operator norm, including at the threshold. -/
theorem analyticAt_cuspGreenCollarTraceOperator (t₀ T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenCollarTraceOperator t₀ T) κ :=
  (differentiable_cuspGreenCollarTraceOperator t₀ T).analyticAt κ

/-- The threshold limit holds in operator norm; its value is the ordinary source-mass functional. -/
theorem cuspGreenCollarTraceOperator_tendsto_zero (t₀ T : ℝ) :
    Tendsto (cuspGreenCollarTraceOperator t₀ T) (𝓝 (0 : ℂ))
      (𝓝 (cuspGreenCollarTraceOperator t₀ T 0)) :=
  (differentiable_cuspGreenCollarTraceOperator t₀ T).continuous.tendsto 0

end GapFamily.Analytic
