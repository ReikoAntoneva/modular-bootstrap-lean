import GapFamily.Analytic.Cusp.Scalar.CuspConstantCollarAnalytic
import GapFamily.Analytic.Cusp.Green.CuspGreenSourceRepresentative
import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponsePencil

/-!
# Actual finite-height continuation of the constant response

The actual source isometry turns the analytic continuous collar profile into
a modular Hilbert vector. Its physical value is the literal height truncation
of the true scalar inverse. Sharp truncation supplies no form-domain claim.
-/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory ModularGradient

/-- An actual finite-height modular L² vector at every parameter, without global W membership. -/
def cuspConstantLocalResponse (T : ℝ) (κ : ℂ) : ModularHilbert :=
  cuspGreenSourceEmbedding T
    (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 T) ℂ (cuspConstantCollarResponse T κ))

theorem cuspConstantLocalResponse_analyticAt (T : ℝ) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) : AnalyticAt ℂ (cuspConstantLocalResponse T) κ := by
  let J : C(CuspGreenCollar 0 T, ℂ) →L[ℂ] ModularHilbert :=
    (cuspGreenSourceEmbedding T).toContinuousLinearMap.comp
      (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 T) ℂ)
  exact (J.analyticAt _).comp_of_eq (cuspConstantCollarResponse_analyticAt T hκ) rfl

theorem cuspConstantLocalResponse_analyticAt_zero (T : ℝ) :
    AnalyticAt ℂ (cuspConstantLocalResponse T) 0 :=
  cuspConstantLocalResponse_analyticAt T (by norm_num)

theorem cuspConstantLocalResponse_ae {T : ℝ} (hT : 0 ≤ T) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) :
    cuspConstantLocalResponse T κ =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im ∧ τ.im ≤ Real.exp T then
        cuspConstantPhysicalResponse κ τ.im else 0) := by
  have hc : Continuous (cuspConstantLogResponse κ) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_cuspConstantLogResponse hκ t).continuousAt)
  have he : cuspConstantCollarResponse T κ =
      (⟨fun t : CuspGreenCollar 0 T => cuspConstantLogResponse κ t,
        hc.comp continuous_subtype_val⟩ : C(CuspGreenCollar 0 T, ℂ)) := by
    ext t
    exact cuspConstantCollarResponse_apply T κ t
  unfold cuspConstantLocalResponse
  rw [he]
  exact cuspGreenSourceEmbedding_continuous_ae T hT _ hc

theorem cuspConstantLocalResponse_eq_lowCut {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) :
    cuspConstantLocalResponse T κ =
      modularLowCut (Real.exp T)
        (scalarCuspEmbedding (cuspScalarPencilSolution ((1 / 4 : ℂ) - κ ^ 2) modularConstant)) := by
  rw [← cuspConstantScalarForm_eq_pencilSolution hκ]
  apply Lp.ext
  have hm : κ ≠ -(1 / 2 : ℂ) := by
    intro he
    rw [he] at hκ
    norm_num at hκ
  filter_upwards [cuspConstantLocalResponse_ae hT hm,
    modularLowCut_ae (Real.exp T) (scalarCuspEmbedding (cuspConstantScalarForm hκ)),
    cuspConstantForm_embedding_ae hκ] with τ hl hc hw
  rw [hl, hc]
  change (if 1 < τ.im ∧ τ.im ≤ Real.exp T then cuspConstantPhysicalResponse κ τ.im else 0) =
    {τ : UpperHalfPlane | τ.im ≤ Real.exp T}.indicator
      (formEmbedding (cuspConstantForm hκ)) τ
  by_cases ht : τ.im ≤ Real.exp T
  · simp only [indicator_apply, mem_ofPred_eq, ht, ite_true, hw, and_true]
  · simp only [indicator_apply, mem_ofPred_eq, ht, ite_false, and_false]

end GapFamily.Analytic
