import GapFamily.Analytic.Foundation.CompactKernelIntegral
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Continuous linear dependence of the actual kernel operator

Integration against a continuous kernel on compact source and target is a complex
continuous linear operation into the operator norm. The construction uses the
ordinary integral operator and its proved integrability, without an operator oracle.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GapFamily.Analytic

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem compactKernelIntegralOperator_add (k l : C(Y × X, ℂ)) :
    compactKernelIntegralOperator μ (k + l) =
      compactKernelIntegralOperator μ k + compactKernelIntegralOperator μ l := by
  ext f y
  simp only [add_apply, ContinuousMap.add_apply,
    compactKernelIntegralOperator_apply, add_mul]
  exact integral_add (compactKernelIntegral_integrable μ k f y)
    (compactKernelIntegral_integrable μ l f y)

theorem compactKernelIntegralOperator_smul (a : ℂ) (k : C(Y × X, ℂ)) :
    compactKernelIntegralOperator μ (a • k) =
      a • compactKernelIntegralOperator μ k := by
  ext f y
  simp only [smul_apply, ContinuousMap.smul_apply,
    compactKernelIntegralOperator_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul a _

/-- The actual kernel integral, bundled linearly in the continuous kernel. -/
def compactKernelOperatorMap :
    C(Y × X, ℂ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] C(Y, ℂ)) :=
  ({ toFun := compactKernelIntegralOperator μ
     map_add' := compactKernelIntegralOperator_add μ
     map_smul' := compactKernelIntegralOperator_smul μ } :
      C(Y × X, ℂ) →ₗ[ℂ] (Lp ℂ 2 μ →L[ℂ] C(Y, ℂ))).mkContinuous
    (Real.sqrt (μ.real univ)) (norm_compactKernelIntegralOperator_le μ)

@[simp]
theorem compactKernelOperatorMap_apply (k : C(Y × X, ℂ)) :
    compactKernelOperatorMap μ k = compactKernelIntegralOperator μ k := rfl

theorem compactKernelOperatorMap_apply_apply (k : C(Y × X, ℂ))
    (f : Lp ℂ 2 μ) (y : Y) :
    compactKernelOperatorMap μ k f y = ∫ x, k (y, x) * f x ∂μ :=
  compactKernelIntegralOperator_apply μ k f y

/-- The source measure gives the norm of integration from uniform kernels. -/
theorem norm_compactKernelOperatorMap_le :
    ‖compactKernelOperatorMap (Y := Y) μ‖ ≤ Real.sqrt (μ.real univ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  exact norm_compactKernelIntegralOperator_le μ

/-- Complex differentiability of kernel integration into the operator norm. -/
theorem differentiable_compactKernelOperatorMap :
    Differentiable ℂ (compactKernelOperatorMap (Y := Y) μ) := by
  exact ContinuousLinearMap.differentiable (𝕜 := ℂ)
    (E := C(Y × X, ℂ)) (F := Lp ℂ 2 μ →L[ℂ] C(Y, ℂ))
    (compactKernelOperatorMap μ)

theorem isCompactOperator_compactKernelOperatorMap_apply (k : C(Y × X, ℂ)) :
    IsCompactOperator (compactKernelOperatorMap μ k) :=
  isCompactOperator_compactKernelIntegralOperator μ k

section TargetL2

variable [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]

/-- The same kernel integral as an operator into the target `L²` space. -/
def compactKernelL2OperatorMap :
    C(Y × X, ℂ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν) :=
  (ContinuousLinearMap.compL ℂ (Lp ℂ 2 μ) C(Y, ℂ) (Lp ℂ 2 ν)
    (ContinuousMap.toLp 2 ν ℂ)).comp (compactKernelOperatorMap μ)

@[simp]
theorem compactKernelL2OperatorMap_apply (k : C(Y × X, ℂ)) :
    compactKernelL2OperatorMap μ ν k =
      (ContinuousMap.toLp 2 ν ℂ).comp (compactKernelIntegralOperator μ k) := rfl

/-- The operator's representatives are the actual ordinary integrals. -/
theorem compactKernelL2OperatorMap_coeFn (k : C(Y × X, ℂ)) (f : Lp ℂ 2 μ) :
    ⇑(compactKernelL2OperatorMap μ ν k f) =ᵐ[ν]
      (fun y => ∫ x, k (y, x) * f x ∂μ) := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ)
    (compactKernelIntegralOperator μ k f)] with y hy
  exact hy.trans (compactKernelIntegralOperator_apply μ k f y)

private theorem norm_continuousMap_toL2_le :
    ‖(ContinuousMap.toLp 2 ν ℂ : C(Y, ℂ) →L[ℂ] Lp ℂ 2 ν)‖ ≤
      Real.sqrt (ν.real univ) := by
  have h := ContinuousMap.toLp_norm_le (p := 2) (E := ℂ) (𝕜 := ℂ) ν
  simp only [ENNReal.toReal_ofNat] at h
  change ‖(ContinuousMap.toLp 2 ν ℂ : C(Y, ℂ) →L[ℂ] Lp ℂ 2 ν)‖ ≤
    (ν.real univ) ^ (2 : ℝ)⁻¹ at h
  simpa only [Real.sqrt_eq_rpow, one_div] using h

/-- Explicit finite-measure bound, uniform in the supplied continuous kernel. -/
theorem norm_compactKernelL2OperatorMap_apply_le (k : C(Y × X, ℂ)) :
    ‖compactKernelL2OperatorMap μ ν k‖ ≤
      (Real.sqrt (ν.real univ) * Real.sqrt (μ.real univ)) * ‖k‖ := by
  rw [compactKernelL2OperatorMap_apply]
  calc
    _ ≤ ‖(ContinuousMap.toLp 2 ν ℂ : C(Y, ℂ) →L[ℂ] Lp ℂ 2 ν)‖ *
        ‖compactKernelIntegralOperator μ k‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.sqrt (ν.real univ) * (Real.sqrt (μ.real univ) * ‖k‖) :=
      mul_le_mul (norm_continuousMap_toL2_le ν)
        (norm_compactKernelIntegralOperator_le μ k) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

theorem norm_compactKernelL2OperatorMap_le :
    ‖compactKernelL2OperatorMap μ ν‖ ≤
      Real.sqrt (ν.real univ) * Real.sqrt (μ.real univ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_compactKernelL2OperatorMap_apply_le μ ν

/-- Complex differentiability also holds in the `L²` operator norm. -/
theorem differentiable_compactKernelL2OperatorMap :
    Differentiable ℂ (compactKernelL2OperatorMap μ ν) := by
  exact ContinuousLinearMap.differentiable (𝕜 := ℂ)
    (E := C(Y × X, ℂ)) (F := Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν)
    (compactKernelL2OperatorMap μ ν)

theorem isCompactOperator_compactKernelL2OperatorMap_apply (k : C(Y × X, ℂ)) :
    IsCompactOperator (compactKernelL2OperatorMap μ ν k) :=
  (isCompactOperator_compactKernelIntegralOperator μ k).clm_comp
    (ContinuousMap.toLp 2 ν ℂ)

end TargetL2

end GapFamily.Analytic
