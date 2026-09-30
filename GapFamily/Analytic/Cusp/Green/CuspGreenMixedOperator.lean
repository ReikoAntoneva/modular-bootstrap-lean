import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorAnalytic
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorTrace

/-!
# Green operators between distinct finite collars

The source and observation collars have independent endpoints. The literal
Green kernel is entire in the uniform kernel norm, hence in both continuous
and `L²` operator norms, including the min-kernel value at zero.
-/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory Filter
open scoped Topology

/-- The actual continuous Green kernel with observation endpoint `L` and source endpoint `T`. -/
def cuspGreenMixedKernel (L T : ℝ) (κ : ℂ) :
    C(CuspGreenCollar 0 L × CuspGreenCollar 0 T, ℂ) :=
  cuspGreenContinuousKernel 0
    ⟨fun p => p.1, continuous_subtype_val.comp continuous_fst⟩
    ⟨fun p => p.2, continuous_subtype_val.comp continuous_snd⟩ κ

@[simp] theorem cuspGreenMixedKernel_apply (L T : ℝ) (κ : ℂ)
    (t : CuspGreenCollar 0 L) (u : CuspGreenCollar 0 T) :
    cuspGreenMixedKernel L T κ (t, u) = cuspGreen 0 t u κ := rfl

/-- The literal response in the uniform norm on the observation collar. -/
def cuspGreenMixedOperator (L T : ℝ) (κ : ℂ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ) :=
  compactKernelOperatorMap (cuspGreenCollarMeasure 0 T) (cuspGreenMixedKernel L T κ)

/-- The same response in the actual unnormalized observation-collar `L²` space. -/
def cuspGreenMixedL2Operator (L T : ℝ) (κ : ℂ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] Lp ℂ 2 (cuspGreenCollarMeasure 0 L) :=
  compactKernelL2OperatorMap (cuspGreenCollarMeasure 0 T)
    (cuspGreenCollarMeasure 0 L) (cuspGreenMixedKernel L T κ)

/-- Every mixed-collar Green integral is ordinarily integrable. -/
theorem cuspGreenMixed_integrable (L T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (t : CuspGreenCollar 0 L) :
    Integrable (fun u : CuspGreenCollar 0 T => cuspGreen 0 t u κ * f u)
      (cuspGreenCollarMeasure 0 T) :=
  compactKernelIntegral_integrable _ (cuspGreenMixedKernel L T κ) f t

theorem cuspGreenMixedOperator_apply (L T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (t : CuspGreenCollar 0 L) :
    cuspGreenMixedOperator L T κ f t =
      ∫ u : CuspGreenCollar 0 T, cuspGreen 0 t u κ * f u ∂cuspGreenCollarMeasure 0 T :=
  compactKernelOperatorMap_apply_apply _ (cuspGreenMixedKernel L T κ) f t

theorem cuspGreenMixedL2Operator_coeFn (L T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    cuspGreenMixedL2Operator L T κ f =ᵐ[cuspGreenCollarMeasure 0 L]
      (fun t => ∫ u : CuspGreenCollar 0 T,
        cuspGreen 0 t u κ * f u ∂cuspGreenCollarMeasure 0 T) :=
  compactKernelL2OperatorMap_coeFn _ _ (cuspGreenMixedKernel L T κ) f

/-- The mixed operator observes the existing actual half-line response. -/
theorem cuspGreenMixedOperator_eq_response (L T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (t : CuspGreenCollar 0 L) :
    cuspGreenMixedOperator L T κ f t = cuspGreenCollarResponse 0 T κ f t :=
  cuspGreenMixedOperator_apply L T κ f t

theorem cuspGreenMixedL2Operator_coeFn_response (L T : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    cuspGreenMixedL2Operator L T κ f =ᵐ[cuspGreenCollarMeasure 0 L]
      (fun t => cuspGreenCollarResponse 0 T κ f t) :=
  cuspGreenMixedL2Operator_coeFn L T κ f

theorem isCompactOperator_cuspGreenMixedOperator (L T : ℝ) (κ : ℂ) :
    IsCompactOperator (cuspGreenMixedOperator L T κ) :=
  isCompactOperator_compactKernelOperatorMap_apply _ _

theorem isCompactOperator_cuspGreenMixedL2Operator (L T : ℝ) (κ : ℂ) :
    IsCompactOperator (cuspGreenMixedL2Operator L T κ) :=
  isCompactOperator_compactKernelL2OperatorMap_apply _ _ _

/-- The true mixed kernel is entire in its uniform spatial norm. -/
theorem differentiable_cuspGreenMixedKernel (L T : ℝ) :
    Differentiable ℂ (cuspGreenMixedKernel L T) :=
  differentiable_cuspGreenContinuousKernel 0 _ _

/-- Entire dependence in the actual continuous-output operator norm. -/
theorem differentiable_cuspGreenMixedOperator (L T : ℝ) :
    Differentiable ℂ (cuspGreenMixedOperator L T) := by
  let M : C(CuspGreenCollar 0 L × CuspGreenCollar 0 T, ℂ) →L[ℂ]
      (Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ)) :=
    compactKernelOperatorMap (cuspGreenCollarMeasure 0 T)
  have h := Differentiable.comp
    (G := Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ))
    (ContinuousLinearMap.differentiable
      (F := Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ)) M)
    (differentiable_cuspGreenMixedKernel L T)
  convert! h using 1

/-- Entire dependence in the actual mixed `L²` operator norm. -/
theorem differentiable_cuspGreenMixedL2Operator (L T : ℝ) :
    Differentiable ℂ (cuspGreenMixedL2Operator L T) := by
  exact (compactKernelL2OperatorMap (cuspGreenCollarMeasure 0 T)
    (cuspGreenCollarMeasure 0 L)).differentiable.comp
      (differentiable_cuspGreenMixedKernel L T)

theorem analyticAt_cuspGreenMixedKernel (L T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenMixedKernel L T) κ :=
  (differentiable_cuspGreenMixedKernel L T).analyticAt κ

theorem analyticAt_cuspGreenMixedOperator (L T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenMixedOperator L T) κ :=
  (differentiable_cuspGreenMixedOperator L T).analyticAt κ

theorem analyticAt_cuspGreenMixedL2Operator (L T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenMixedL2Operator L T) κ :=
  (differentiable_cuspGreenMixedL2Operator L T).analyticAt κ

/-- The entire extension retains the literal min-kernel at the threshold. -/
theorem cuspGreenMixedOperator_zero_apply (L T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (t : CuspGreenCollar 0 L) :
    cuspGreenMixedOperator L T 0 f t =
      ∫ u : CuspGreenCollar 0 T, ((min (t : ℝ) (u : ℝ) : ℝ) : ℂ) * f u
        ∂cuspGreenCollarMeasure 0 T := by
  simp only [cuspGreenMixedOperator_apply, cuspGreen_zero, sub_zero]

theorem cuspGreenMixedL2Operator_tendsto_zero (L T : ℝ) :
    Tendsto (cuspGreenMixedL2Operator L T) (𝓝 (0 : ℂ))
      (𝓝 (cuspGreenMixedL2Operator L T 0)) :=
  (differentiable_cuspGreenMixedL2Operator L T).continuous.tendsto 0

end GapFamily.Analytic
