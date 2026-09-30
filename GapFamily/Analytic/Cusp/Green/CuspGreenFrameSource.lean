import GapFamily.Analytic.Cusp.Green.CuspGreenFirstSmooth
import GapFamily.Analytic.Cusp.Green.CuspGreenSmoothGradient
import GapFamily.Analytic.Cusp.Green.CuspGreenScalarResponse
import GapFamily.Analytic.Cusp.Green.CuspGreenCollarOutput

/-!
# Closed physical gradient of every collar-source Green response

The continuous shifted derivative is embedded by the actual collar isometry.
Identification on smooth sources extends by their proved density to all source
classes. No regularity of an arbitrary `L²` source is assumed.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient
open scoped Topology ContDiff

/-- The physical vertical-frame output, restricted to a finite observation height. -/
def cuspGreenFrameSourceOperator (L T : ℝ) (κ : ℂ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] ModularHilbert :=
  ((cuspGreenSourceEmbedding L).toContinuousLinearMap.comp
    (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ)).comp
      (cuspGreenFrameOperator L T κ)

theorem differentiable_cuspGreenFrameSourceOperator (L T : ℝ) :
    Differentiable ℂ (cuspGreenFrameSourceOperator L T) :=
  (differentiable_const ((cuspGreenSourceEmbedding L).toContinuousLinearMap.comp
    (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ))).clm_comp
      (differentiable_cuspGreenFrameOperator L T)

theorem analyticAt_cuspGreenFrameSourceOperator (L T : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreenFrameSourceOperator L T) κ :=
  (differentiable_cuspGreenFrameSourceOperator L T).analyticAt κ

/-- The actual smooth-source graph gradient equals the continued frame output. -/
theorem cuspGreenFrameSourceOperator_smooth {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioo 0 T) :
    cuspGreenFrameSourceOperator L T κ (cuspGreenCollarSource 0 T f hf.continuous) =
      modularLowCut (Real.exp L) (formGradient (cuspGreenSmoothForm hT hκ hf hs)).ofLp.2 := by
  have hk : κ ≠ 0 := by intro h; simp [h] at hκ
  have hrep := cuspGreenSourceEmbedding_toLp_ae L hL
    (cuspGreenFrameOperator L T κ (cuspGreenCollarSource 0 T f hf.continuous))
    (fun t => cuspGreenSolutionFormulaDeriv 0 T κ f t +
      (1 / 2 : ℂ) * cuspGreenSolutionFormula 0 T κ f t)
    (fun t => cuspGreenFrameOperator_apply_source hT hk hf.continuous hs t)
  apply Lp.ext
  filter_upwards [hrep, modularLowCut_ae (Real.exp L)
      (formGradient (cuspGreenSmoothForm hT hκ hf hs)).ofLp.2,
    cuspGreenSmoothForm_gradient_snd_ae hT hκ hf hs] with τ hout hcut hgrad
  change cuspGreenSourceEmbedding L
    (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ
      (cuspGreenFrameOperator L T κ (cuspGreenCollarSource 0 T f hf.continuous))) τ = _
  rw [hout, hcut]
  by_cases ht : τ.im ≤ Real.exp L
  · simp only [indicator_apply, mem_ofPred_eq, ht, ite_true, hgrad, and_true]
  · simp only [indicator_apply, mem_ofPred_eq, ht, ite_false, and_false]

/-- Every genuine `L²` source has this clipped closed vertical gradient in the physical half-plane. -/
theorem cuspGreenFrameSourceOperator_eq_physical {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    cuspGreenFrameSourceOperator L T κ f = modularLowCut (Real.exp L)
      (cuspScalarGradient (cuspGreenScalarFormOperator T κ f)).ofLp.2 := by
  let B : Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] ModularHilbert :=
    (modularLowCut (Real.exp L)).comp
      (((WithLp.sndL 2 ℂ ModularHilbert ModularHilbert).comp cuspScalarGradient).comp
        (cuspGreenScalarFormOperator T κ))
  change cuspGreenFrameSourceOperator L T κ f = B f
  refine (cuspGreenSourceRestriction_denseRange T).induction_on f
    (isClosed_eq (cuspGreenFrameSourceOperator L T κ).continuous B.continuous) ?_
  intro p
  change cuspGreenFrameSourceOperator L T κ
      (cuspGreenCollarSource 0 T (p : ℝ → ℂ) p.property.1.continuous) =
    modularLowCut (Real.exp L) (cuspScalarGradient
      (cuspGreenScalarFormOperator T κ
        (cuspGreenCollarSource 0 T (p : ℝ → ℂ) p.property.1.continuous))).ofLp.2
  rw [cuspGreenScalarFormOperator_smooth hT hκ p.property.1 p.property.2.1 p.property.2.2]
  exact cuspGreenFrameSourceOperator_smooth hL hT hκ p.property.1 p.property.2.2

end GapFamily.Analytic
