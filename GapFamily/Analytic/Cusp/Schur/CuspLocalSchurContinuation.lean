import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurBasic

/-!
# Operator-norm continuation of the local Schur family

Actual constrained quarter regularity and the continued nonzero denominator,
together with the proved local response maps, give analytic bounded operators
through threshold. Physical identification is proved in the companion module.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal
open Filter
open scoped Topology

private theorem analyticAt_comp_clm
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {a : ℂ} {f : ℂ → (F →L[ℂ] G)} {g : ℂ → (E →L[ℂ] F)}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) :
    AnalyticAt ℂ (fun z => (f z).comp (g z)) a :=
  ((ContinuousLinearMap.compL ℂ E F G).analyticAt_bilinear _).comp (hf.prod hg)

theorem parameter_analyticAt (κ : ℂ) : AnalyticAt ℂ parameter κ := by
  unfold parameter
  fun_prop

theorem constrainedResponse_analyticAt_zero : AnalyticAt ℂ constrainedResponse 0 := by
  have hs : AnalyticAt ℂ (fun κ => cuspMeanZeroPencilSolution (parameter κ)) 0 := by
    apply (cuspMeanZeroPencilSolution_analyticAt cuspMeanZeroPencil_isUnit_quarter).comp_of_eq
      (parameter_analyticAt 0)
    norm_num [parameter]
  let P : (ModularHilbert →L[ℂ] cuspMeanZeroForm) →L[ℂ]
      (ModularHilbert →L[ℂ] ModularHilbert) :=
    ContinuousLinearMap.compL ℂ ModularHilbert cuspMeanZeroForm ModularHilbert
      meanZeroCuspEmbedding
  have hP := ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := ModularHilbert →L[ℂ] cuspMeanZeroForm)
    (F := ModularHilbert →L[ℂ] ModularHilbert) P
      (cuspMeanZeroPencilSolution (parameter 0))
  exact hP.comp_of_eq hs rfl

theorem localZeroTrace_analyticAt_zero (L T : ℝ) :
    AnalyticAt ℂ (localZeroTrace L T) 0 :=
  (analyticAt_comp_clm
    (analyticAt_comp_clm analyticAt_const constrainedResponse_analyticAt_zero)
    analyticAt_const).add (analyticAt_cuspGreenLocalizedOutput L T 0)

theorem localNumerator_analyticAt_zero (T : ℝ) : AnalyticAt ℂ (localNumerator T) 0 := by
  exact analyticAt_comp_clm
    (analyticAt_const.add ((parameter_analyticAt 0).smul
      ((analyticAt_comp_clm analyticAt_const constrainedResponse_analyticAt_zero).add
        (cuspConstantPairingFunctional_analyticAt_zero T)))) analyticAt_const

theorem localTraceVector_analyticAt_zero (L : ℝ) :
    AnalyticAt ℂ (localTraceVector L) 0 := by
  have hq : AnalyticAt ℂ (fun κ => constrainedResponse κ modularConstant) 0 :=
    ((ContinuousLinearMap.apply ℂ ModularHilbert modularConstant).analyticAt _).comp
      constrainedResponse_analyticAt_zero
  have hl : AnalyticAt ℂ
      (fun κ => modularLowCut (Real.exp L) (constrainedResponse κ modularConstant)) 0 :=
    ((modularLowCut (Real.exp L)).analyticAt _).comp hq
  exact analyticAt_const.add ((parameter_analyticAt 0).smul
    (hl.add (cuspConstantLocalResponse_analyticAt_zero L)))

/-- Genuine operator-norm continuation through threshold of the locally compressed Schur response. -/
theorem continuedLocalSchur_analyticAt_zero (L T : ℝ) :
    AnalyticAt ℂ (continuedLocalSchur L T) 0 := by
  have hc := CuspSchur.continuedDenominator_inverse_analyticAt_threshold.smul
    (localNumerator_analyticAt_zero T)
  have hp := hc.prod (localTraceVector_analyticAt_zero L)
  have hR := (ContinuousLinearMap.smulRightL ℂ ModularHilbert ModularHilbert).analyticAt_bilinear
    (((CuspSchur.continuedDenominator 0)⁻¹ • localNumerator T 0), localTraceVector L 0)
  have hr := hR.comp_of_eq hp rfl
  exact (localZeroTrace_analyticAt_zero L T).add hr

/-- The continued value is an actual limit in the bounded-operator norm. -/
theorem continuedLocalSchur_tendsto_zero (L T : ℝ) :
    Tendsto (continuedLocalSchur L T) (𝓝 (0 : ℂ)) (𝓝 (continuedLocalSchur L T 0)) :=
  (continuedLocalSchur_analyticAt_zero L T).continuousAt.tendsto

end GapFamily.Analytic.CuspSchurLocal
