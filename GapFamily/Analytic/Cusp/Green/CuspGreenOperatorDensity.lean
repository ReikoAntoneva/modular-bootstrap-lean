import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorBasic
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Actual continuous collar sources determine the bounded Green extension uniquely. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set

/-- Continuous collar functions are dense in the literal collar L² space. -/
theorem denseRange_cuspGreenCollar_continuousSource (t₀ T : ℝ) :
    DenseRange (ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ :
      C(CuspGreenCollar t₀ T, ℂ) →L[ℂ] Lp ℂ 2 (cuspGreenCollarMeasure t₀ T)) :=
  ContinuousMap.toLp_denseRange ℂ (cuspGreenCollarMeasure t₀ T) ℂ (by norm_num)

/-- On an actual continuous source, the operator is its literal ordinary kernel integral. -/
theorem cuspGreenCollarOperator_apply_continuous (t₀ T : ℝ) (κ : ℂ)
    (f : C(CuspGreenCollar t₀ T, ℂ)) (t : CuspGreenCollar t₀ T) :
    cuspGreenCollarOperator t₀ T κ
        (ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ f) t =
      ∫ u : CuspGreenCollar t₀ T, cuspGreen t₀ t u κ * f u ∂cuspGreenCollarMeasure t₀ T := by
  rw [cuspGreenCollarOperator_apply]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := cuspGreenCollarMeasure t₀ T)
    (𝕜 := ℂ) f] with u hu
  rw [hu]

/-- A bounded map on collar L² is uniquely determined by its continuous-source values. -/
theorem cuspGreenCollarOperator_ext_continuousSource (t₀ T : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A B : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) →L[ℂ] F}
    (h : ∀ f : C(CuspGreenCollar t₀ T, ℂ),
      A (ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ f) =
        B (ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ f)) : A = B := by
  apply DFunLike.coe_injective
  exact (denseRange_cuspGreenCollar_continuousSource t₀ T).equalizer
    A.continuous B.continuous (funext h)

/-- The constructed Green operator is the unique bounded extension of the literal integral. -/
theorem cuspGreenCollarOperator_unique (t₀ T : ℝ) (κ : ℂ)
    (A : Lp ℂ 2 (cuspGreenCollarMeasure t₀ T) →L[ℂ] C(CuspGreenCollar t₀ T, ℂ))
    (hA : ∀ (f : C(CuspGreenCollar t₀ T, ℂ)) (t : CuspGreenCollar t₀ T),
      A (ContinuousMap.toLp 2 (cuspGreenCollarMeasure t₀ T) ℂ f) t =
        ∫ u : CuspGreenCollar t₀ T, cuspGreen t₀ t u κ * f u ∂cuspGreenCollarMeasure t₀ T) :
    A = cuspGreenCollarOperator t₀ T κ := by
  apply cuspGreenCollarOperator_ext_continuousSource t₀ T
  intro f
  ext t
  exact (hA f t).trans (cuspGreenCollarOperator_apply_continuous t₀ T κ f t).symm

end GapFamily.Analytic
