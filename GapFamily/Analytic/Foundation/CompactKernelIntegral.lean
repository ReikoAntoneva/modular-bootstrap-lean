import GapFamily.Analytic.Foundation.CompactKernelIntegralAscoli
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Compact operators from actual continuous kernel integrals

A kernel family continuous in the uniform norm supplies a continuous field
of actual `L²` sections. The field's inner products give precisely the
ordinary kernel integrals. Arzelà–Ascoli proves compactness internally.
-/

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate ENNReal BoundedContinuousFunction

namespace GapFamily.Analytic

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y]

section BoundedKernel

variable (μ : Measure X) [IsFiniteMeasure μ] (k : C(Y, X →ᵇ ℂ))

/-- The actual conjugated kernel sections in the source Hilbert space. -/
def boundedKernelL2Field : C(Y, Lp ℂ 2 μ) :=
  ⟨fun y => BoundedContinuousFunction.toLp 2 μ ℂ (star (k y)),
    (BoundedContinuousFunction.toLp 2 μ ℂ).continuous.comp (map_continuous (star k))⟩

omit [CompactSpace Y] in
/-- The Hilbert section represents the pointwise conjugate of the supplied kernel. -/
theorem boundedKernelL2Field_coeFn (y : Y) :
    ⇑(boundedKernelL2Field μ k y) =ᵐ[μ] (fun x => conj (k y x)) :=
  BoundedContinuousFunction.coeFn_toLp 2 μ ℂ (star (k y))

/-- The actual kernel integral defines a continuous function on the compact target. -/
def boundedKernelIntegralOperator : Lp ℂ 2 μ →L[ℂ] C(Y, ℂ) :=
  innerFieldOperator (boundedKernelL2Field μ k)

omit [CompactSpace Y] in
/-- Every integral used in the operator is genuinely integrable. -/
theorem boundedKernelIntegral_integrable (f : Lp ℂ 2 μ) (y : Y) :
    Integrable (fun x => k y x * f x) μ := by
  apply (L2.integrable_inner (boundedKernelL2Field μ k y) f).congr
  filter_upwards [boundedKernelL2Field_coeFn μ k y] with x hx
  simp only [RCLike.inner_apply', hx, starRingEnd_self_apply]

/-- Exact identification with the ordinary integral, with no integral oracle. -/
theorem boundedKernelIntegralOperator_apply (f : Lp ℂ 2 μ) (y : Y) :
    boundedKernelIntegralOperator μ k f y = ∫ x, k y x * f x ∂μ := by
  rw [boundedKernelIntegralOperator, innerFieldOperator_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedKernelL2Field_coeFn μ k y] with x hx
  simp only [RCLike.inner_apply', hx, starRingEnd_self_apply]

/-- Compactness follows from the supplied kernel's actual uniform-norm continuity. -/
theorem isCompactOperator_boundedKernelIntegralOperator :
    IsCompactOperator (boundedKernelIntegralOperator μ k) :=
  isCompactOperator_innerFieldOperator (boundedKernelL2Field μ k)

private theorem norm_boundedContinuous_toL2_le :
    ‖(BoundedContinuousFunction.toLp 2 μ ℂ : (X →ᵇ ℂ) →L[ℂ] Lp ℂ 2 μ)‖ ≤
      Real.sqrt (μ.real univ) := by
  have h := BoundedContinuousFunction.toLp_norm_le (p := 2) (E := ℂ) (𝕜 := ℂ) μ
  simp only [ENNReal.toReal_ofNat] at h
  change ‖(BoundedContinuousFunction.toLp 2 μ ℂ : (X →ᵇ ℂ) →L[ℂ] Lp ℂ 2 μ)‖ ≤
    (μ.real univ) ^ (2 : ℝ)⁻¹ at h
  simpa only [Real.sqrt_eq_rpow, one_div] using h

/-- Explicit uniform bound for the actual kernel field. -/
theorem norm_boundedKernelL2Field_le :
    ‖boundedKernelL2Field μ k‖ ≤ Real.sqrt (μ.real univ) * ‖k‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro y
  change ‖BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ (star (k y))‖ ≤ _
  calc
    _ ≤ ‖(BoundedContinuousFunction.toLp 2 μ ℂ : (X →ᵇ ℂ) →L[ℂ] Lp ℂ 2 μ)‖ *
        ‖star (k y)‖ :=
      (BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ).le_opNorm (star (k y))
    _ ≤ Real.sqrt (μ.real univ) * ‖k‖ := by
      rw [norm_star]
      exact mul_le_mul (norm_boundedContinuous_toL2_le μ) (k.norm_coe_le_norm y)
        (norm_nonneg _) (Real.sqrt_nonneg _)

/-- Cauchy–Schwarz gives the standard finite-measure operator norm bound. -/
theorem norm_boundedKernelIntegralOperator_le :
    ‖boundedKernelIntegralOperator μ k‖ ≤ Real.sqrt (μ.real univ) * ‖k‖ :=
  (norm_innerFieldOperator_le (boundedKernelL2Field μ k)).trans
    (norm_boundedKernelL2Field_le μ k)

variable [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]

/-- The same ordinary kernel gives an actual compact operator between `L²` spaces. -/
def boundedKernelIntegralL2Operator : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν :=
  (ContinuousMap.toLp 2 ν ℂ).comp (boundedKernelIntegralOperator μ k)

theorem isCompactOperator_boundedKernelIntegralL2Operator :
    IsCompactOperator (boundedKernelIntegralL2Operator μ k ν) :=
  (isCompactOperator_boundedKernelIntegralOperator μ k).clm_comp (ContinuousMap.toLp 2 ν ℂ)

/-- The target `L²` class is represented by the actual ordinary kernel integrals. -/
theorem boundedKernelIntegralL2Operator_coeFn (f : Lp ℂ 2 μ) :
    ⇑(boundedKernelIntegralL2Operator μ k ν f) =ᵐ[ν]
      (fun y => ∫ x, k y x * f x ∂μ) := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ) (boundedKernelIntegralOperator μ k f)] with y hy
  exact hy.trans (boundedKernelIntegralOperator_apply μ k f y)

end BoundedKernel

section CompactSource

variable [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ] (k : C(Y × X, ℂ))

/-- Joint continuity on the compact source gives the required uniform-norm kernel family. -/
def compactKernelFamily : C(Y, X →ᵇ ℂ) :=
  ⟨fun y => ContinuousMap.linearIsometryBoundedOfCompact X ℂ ℂ (k.curry y),
    (ContinuousMap.linearIsometryBoundedOfCompact X ℂ ℂ).continuous.comp k.curry.continuous⟩

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace Y] in
@[simp]
theorem compactKernelFamily_apply (y : Y) (x : X) :
    compactKernelFamily k y x = k (y, x) := rfl

/-- The actual continuous-kernel integral operator on compact source and target. -/
def compactKernelIntegralOperator : Lp ℂ 2 μ →L[ℂ] C(Y, ℂ) :=
  boundedKernelIntegralOperator μ (compactKernelFamily k)

omit [CompactSpace Y] in
theorem compactKernelIntegral_integrable (f : Lp ℂ 2 μ) (y : Y) :
    Integrable (fun x => k (y, x) * f x) μ :=
  boundedKernelIntegral_integrable μ (compactKernelFamily k) f y

theorem compactKernelIntegralOperator_apply (f : Lp ℂ 2 μ) (y : Y) :
    compactKernelIntegralOperator μ k f y = ∫ x, k (y, x) * f x ∂μ :=
  boundedKernelIntegralOperator_apply μ (compactKernelFamily k) f y

/-- No equicontinuity or compact-image premise is needed beyond kernel continuity. -/
theorem isCompactOperator_compactKernelIntegralOperator :
    IsCompactOperator (compactKernelIntegralOperator μ k) :=
  isCompactOperator_boundedKernelIntegralOperator μ (compactKernelFamily k)

omit [MeasurableSpace X] [BorelSpace X] in
theorem norm_compactKernelFamily_le : ‖compactKernelFamily k‖ ≤ ‖k‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg k)).mpr
  intro y
  apply (BoundedContinuousFunction.norm_le (norm_nonneg k)).mpr
  intro x
  exact k.norm_coe_le_norm (y, x)

theorem norm_compactKernelIntegralOperator_le :
    ‖compactKernelIntegralOperator μ k‖ ≤ Real.sqrt (μ.real univ) * ‖k‖ :=
  (norm_boundedKernelIntegralOperator_le μ (compactKernelFamily k)).trans
    (mul_le_mul_of_nonneg_left (norm_compactKernelFamily_le k) (Real.sqrt_nonneg _))

end CompactSource

end GapFamily.Analytic
