import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedLocal
import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedPrimitive
import GapFamily.Analytic.Cusp.Green.CuspGreenTailFrameOperator
import GapFamily.Analytic.Cusp.Green.CuspGreenTailPrimitive
import GapFamily.Analytic.Cusp.Green.CuspGreenFrameOutput

/-! The actual shifted logarithmic derivative on a finite observation collar,
formed from the existing finite-source frame operator and its genuine tail. -/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory CuspHalfLineLaplace CuspHalfLineLaplaceTail
open scoped Topology

def cuspGreenWeightedFrameLocalOperator (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) (κ : ℂ) :
    HalfLineL2 →L[ℂ] C(CuspGreenCollar 0 L, ℂ) :=
  (cuspGreenFrameOperator L T κ).comp
      ((cuspHalfLineCollarRestriction T).comp (cuspHalfLineWeight α hα)) +
    cuspGreenWeightedTailFrameOperator α L T κ

theorem analyticAt_cuspGreenWeightedFrameLocalOperator (α : ℝ) (hα : 0 ≤ α) (L T : ℝ)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) :
    AnalyticAt ℂ (cuspGreenWeightedFrameLocalOperator α hα L T) κ := by
  have hf : AnalyticAt ℂ (fun z : ℂ => (cuspGreenFrameOperator L T z).comp
      ((cuspHalfLineCollarRestriction T).comp (cuspHalfLineWeight α hα))) κ :=
    ((differentiable_cuspGreenFrameOperator L T).clm_comp
      (differentiable_const ((cuspHalfLineCollarRestriction T).comp
        (cuspHalfLineWeight α hα)))).analyticAt κ
  exact hf.add (analyticAt_cuspGreenWeightedTailFrameOperator α L T hβ)

theorem analyticAt_cuspGreenWeightedFrameLocalOperator_zero {α : ℝ} (hα : 0 < α)
    (L T : ℝ) : AnalyticAt ℂ (cuspGreenWeightedFrameLocalOperator α hα.le L T) 0 :=
  analyticAt_cuspGreenWeightedFrameLocalOperator α hα.le L T (by simpa using hα)

/-- The tail correction reconstructs the actual trace-plus-primitive formula.
All source primitives and the shifted Laplace trace are ordinary convergent integrals. -/
theorem cuspGreenWeightedFrameLocalOperator_apply_trace {α L T : ℝ} (hα : 0 ≤ α)
    (hT : 0 ≤ T) (hLT : L ≤ T) {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re)
    (f : HalfLineL2) (t : CuspGreenCollar 0 L) :
    cuspGreenWeightedFrameLocalOperator α hα L T κ f t =
      laplace ((α : ℂ) + κ) f + κ ^ 2 *
        cuspCollarPrimitive L L (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ
          (cuspGreenWeightedLocalOperator α hα L T κ f)) t -
        cuspCollarPrimitive L L (cuspHalfLineCollarRestriction L (cuspHalfLineWeight α hα f)) t +
        (1 / 2 : ℂ) * cuspGreenWeightedLocalOperator α hα L T κ f t := by
  let q := cuspHalfLineCollarRestriction T (cuspHalfLineWeight α hα f)
  let r := tailLaplace T ((α : ℂ) + κ) f
  have hv : cuspGreenWeightedLocalOperator α hα L T κ f =
      cuspGreenMixedOperator L T κ q + r • cuspGreenTailObserved L κ := rfl
  have hp := cuspCollarPrimitive_cuspGreenTailObserved_eq_cosh L κ t
  have hs := cuspGreenWeighted_laplace_split hα hT hβ f
  have hsource := congrArg (fun g : C(CuspGreenCollar 0 L, ℂ) => g t)
    (cuspCollarPrimitive_halfLineRestriction_cutoff_eq hLT (cuspHalfLineWeight α hα f))
  change cuspGreenFrameOperator L T κ q t + cuspGreenWeightedTailFrameOperator α L T κ f t = _
  rw [cuspGreenFrameOperator_apply, cuspGreenFirstOperator_apply,
    cuspGreenWeightedTailFrameOperator_apply, cuspGreenTailFrameValue, hs, hv]
  simp only [map_add, map_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    smul_eq_mul, cuspGreenTailObserved_apply]
  have hl2 : cuspGreenMixedL2Operator L T κ q =
      ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ (cuspGreenMixedOperator L T κ q) := rfl
  rw [hl2]
  change cuspCollarPrimitive L T q t =
    cuspCollarPrimitive L L (cuspHalfLineCollarRestriction L (cuspHalfLineWeight α hα f)) t at hsource
  rw [← hsource]
  change cuspGreenCollarTraceOperator 0 T κ q + κ ^ 2 *
      cuspCollarPrimitive L L
        (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ
          (cuspGreenMixedOperator L T κ q)) t - cuspCollarPrimitive L T q t +
      (1 / 2 : ℂ) * cuspGreenMixedOperator L T κ q t +
      (Complex.cosh (κ * (t : ℝ)) + (1 / 2 : ℂ) * cuspGreenTailValue t κ) * r = _
  linear_combination -r * hp

/-- The genuine local gradient profile is independent of the auxiliary source cutoff. -/
theorem cuspGreenWeightedFrameLocalOperator_cutoff_eq {α L T R : ℝ} (hα : 0 ≤ α)
    (hT : 0 ≤ T) (hLT : L ≤ T) (hR : 0 ≤ R) (hLR : L ≤ R)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) :
    cuspGreenWeightedFrameLocalOperator α hα L T κ =
      cuspGreenWeightedFrameLocalOperator α hα L R κ := by
  apply ContinuousLinearMap.ext
  intro f
  ext t
  rw [cuspGreenWeightedFrameLocalOperator_apply_trace hα hT hLT hβ,
    cuspGreenWeightedFrameLocalOperator_apply_trace hα hR hLR hβ,
    cuspGreenWeightedLocalOperator_cutoff_eq hα hT hLT hR hLR hβ]

/-- The actual physical vertical-frame output in modular L². -/
def cuspGreenWeightedFrameLocalOutput (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) (κ : ℂ) :
    HalfLineL2 →L[ℂ] ModularHilbert :=
  (cuspGreenSourceEmbedding L).toContinuousLinearMap.comp
    ((ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ).comp
      (cuspGreenWeightedFrameLocalOperator α hα L T κ))

theorem analyticAt_cuspGreenWeightedFrameLocalOutput (α : ℝ) (hα : 0 ≤ α) (L T : ℝ)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) :
    AnalyticAt ℂ (cuspGreenWeightedFrameLocalOutput α hα L T) κ := by
  let P : C(CuspGreenCollar 0 L, ℂ) →L[ℂ] ModularHilbert :=
    (cuspGreenSourceEmbedding L).toContinuousLinearMap.comp
      (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ)
  exact ((ContinuousLinearMap.compL ℂ HalfLineL2 C(CuspGreenCollar 0 L, ℂ)
    ModularHilbert P).analyticAt _).comp
      (analyticAt_cuspGreenWeightedFrameLocalOperator α hα L T hβ)

theorem analyticAt_cuspGreenWeightedFrameLocalOutput_zero {α : ℝ} (hα : 0 < α)
    (L T : ℝ) : AnalyticAt ℂ (cuspGreenWeightedFrameLocalOutput α hα.le L T) 0 :=
  analyticAt_cuspGreenWeightedFrameLocalOutput α hα.le L T (by simpa using hα)

end GapFamily.Analytic
