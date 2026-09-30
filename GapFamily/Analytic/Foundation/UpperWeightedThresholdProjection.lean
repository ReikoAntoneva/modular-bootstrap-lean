import GapFamily.Analytic.Foundation.UpperWeightedJetContinuation
import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurCoherence

/-! The continued local Poisson jet retains the literal finite-height Schur value at zero. -/
noncomputable section
namespace GapFamily.Analytic.UpperWeightedThresholdValue
open Set Filter MeasureTheory ModularGradient UpperHalfPlane CuspSchurLocal
  UpperWeighted UpperWeightedJet UpperSource LocalPoisson
open scoped Topology ContDiff

/-- Genuine physical agreement identifies the value projection of the
constructed threshold jet with the explicit weighted local Schur operator.
The absorption height and all jet data are constructed. -/
theorem exists_continuedJet_with_explicit_value
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    {α : ℝ} (hα : 0 < α) :
    ∃ (L : ℝ), 0 ≤ L ∧
      (upperCutoffHilbertValueOperator χ hχ hc hs).comp (modularLowCut (Real.exp L)) =
        upperCutoffHilbertValueOperator χ hχ hc hs ∧ ∃ (A : ℂ → ModularHilbert →L[ℂ] Jet)
      (Q : ℂ → ModularHilbert →L[ℂ] JetSpace U) (r : ℝ), 0 < r ∧
      AnalyticOnNhd ℂ A (Metric.ball 0 r) ∧ AnalyticOnNhd ℂ Q (Metric.ball 0 r) ∧
      (∀ κ : ℂ, ‖κ‖ < r →
        (jetSubmodule U).subtypeL.comp (Q κ) = A κ ∧
        (0 < κ.re → ∀ f : ModularHilbert,
          ∃ hu : CuspSchur.actualSchurResolvent (parameter κ)
              (cuspWeightedInput α hα.le f) ∈ laplacian.domain,
            A κ f = actualJet χ hχ hc hs
              ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu⟩)) ∧
      (valueCLM U).comp (Q 0) = upperWeightedSchurValue χ hχ hc hs α hα.le L 0 := by
  obtain ⟨A, Q, r, hr, hA, hQ, hcoordinates⟩ :=
    exists_analytic_continuedJet χ hχ hc hs U hU hχU hα
  obtain ⟨L, hL, _Bx, _By, hAbs, _hDx, _hDy⟩ :=
    WeightedSeam.exists_upperCutoff_common_height χ hχ hc hs
  have hV := upperWeightedSchurValue_analyticAt_zero χ hχ hc hs hα L
  have hQ0 : AnalyticAt ℂ Q 0 := hQ 0 (Metric.mem_ball_self hr)
  let P : (ModularHilbert →L[ℂ] JetSpace U) →L[ℂ] (ModularHilbert →L[ℂ] Field) :=
    ContinuousLinearMap.compL ℂ ModularHilbert (JetSpace U) Field (valueCLM U)
  have hp : AnalyticAt ℂ (fun κ => (valueCLM U).comp (Q κ)) 0 :=
    by
      change AnalyticAt ℂ (fun κ => P (Q κ)) 0
      exact (P.analyticAt (Q 0)).comp hQ0
  have heq : (fun κ => (valueCLM U).comp (Q κ)) =ᶠ[𝓝 (0 : ℂ)]
      upperWeightedSchurValue χ hχ hc hs α hα.le L := by
    apply CuspSchurCoherence.analyticAt_eventuallyEq_of_physical hp hV
    refine ⟨min r (1 / 2), lt_min hr (by norm_num), ?_⟩
    intro κ hn hκ
    have hnr : ‖κ‖ < r := hn.trans_le (min_le_left _ _)
    have hh : κ ≠ (1 / 2 : ℂ) := by
      intro he
      have hn2 := hn.trans_le (min_le_right r (1 / 2))
      rw [he] at hn2
      norm_num at hn2
    apply ContinuousLinearMap.ext
    intro f
    obtain ⟨hsub, hphysical⟩ := hcoordinates κ hnr
    obtain ⟨hu, hj⟩ := hphysical hκ f
    let u : laplacian.domain :=
      ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu⟩
    have hq : Q κ f = ⟨actualJet χ hχ hc hs u, actualJet_mem χ hχ hc hs U hU hχU u⟩ := by
      apply Subtype.ext
      exact (congrArg (fun T : ModularHilbert →L[ℂ] Jet => T f) hsub).trans hj
    change valueCLM U (Q κ f) = upperWeightedSchurValue χ hχ hc hs α hα.le L κ f
    rw [hq]
    change upperCutoffValueOperator χ hχ hc hs (formLift ⟨u, laplacian_domain_le u.property⟩) = _
    have hform : formLift ⟨u, laplacian_domain_le u.property⟩ =
        CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f) := by
      apply formEmbedding_injective
      rfl
    rw [hform]
    exact (upperWeightedSchurValue_eq_physical χ hχ hc hs hα hL hAbs hκ hh f).symm
  exact ⟨L, hL, hAbs, A, Q, r, hr, hA, hQ, hcoordinates, heq.self_of_nhds⟩

end GapFamily.Analytic.UpperWeightedThresholdValue
