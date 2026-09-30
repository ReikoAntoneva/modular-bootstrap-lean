import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurEvaluation

noncomputable section
namespace GapFamily.Analytic.CuspFourierCutoff
open Set ModularGradient Dirichlet

/-- Apply the actual finite-height local inverse to a genuinely analytic source family.
The final compact Fourier theorem below supplies both hypotheses explicitly. -/
theorem exists_analytic_heightSupportedResponse
    (F : ℂ → ModularHilbert) (hF : AnalyticAt ℂ F 0)
    (hheight : ∀ κ, modularLowCut 3 (F κ) = F κ)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ modularInterior)
    (hreg : K ⊆ closure (interior K)) :
    ∃ (U : ℂ → C(K, ℂ)) (ε : ℝ), 0 < ε ∧ AnalyticAt ℂ U 0 ∧
      ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re →
        ∃ hu : CuspSchur.actualSchurResolvent (CuspSchurLocal.parameter κ) (F κ) ∈
            laplacian.domain,
          U κ = laplacianLocalRestriction K hKU hreg (gradientLift laplacian
            ⟨CuspSchur.actualSchurResolvent (CuspSchurLocal.parameter κ) (F κ), hu⟩) := by
  obtain ⟨E, ε, hε, hE, hphysical⟩ :=
    CuspSchurLocal.exists_analytic_localSchurEvaluation K hKU hreg
      (T := Real.log 3) (Real.log_nonneg (by norm_num))
  refine ⟨fun κ => E κ (F κ), ε, hε, ?_, ?_⟩
  · exact ((ContinuousLinearMap.apply ℂ C(K, ℂ)).analyticAt_bilinear
      (F 0, E 0)).comp_of_eq (hF.prod hE) rfl
  · intro κ hκ hpos
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3), hheight κ] using
      hphysical κ hκ hpos (F κ)

end GapFamily.Analytic.CuspFourierCutoff
