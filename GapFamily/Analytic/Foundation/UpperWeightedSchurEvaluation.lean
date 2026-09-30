import GapFamily.Analytic.Foundation.UpperWeightedJetContinuation
import GapFamily.Analytic.Elliptic.LocalPoissonEvaluation
import GapFamily.Analytic.Modular.Elliptic.ModularUpperCompactEvaluation

noncomputable section
namespace GapFamily.Analytic.UpperWeightedJet
open Set Filter MeasureTheory ModularGradient UpperHalfPlane CuspSchurLocal Dirichlet
open UpperSource LocalPoisson
open scoped ContDiff Topology

/-- The actual jet's continuous representative is the already proved actual
modular graph representative, including on thin compact observation sets. -/
theorem actualJet_restriction
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (u : laplacian.domain) :
    restriction U hU K hKU ⟨actualJet χ hχ hc hs u, actualJet_mem χ hχ hc hs U hU hχU u⟩ =
      laplacianUpperCompactRestriction χ hχ hc hs U hU hχU K hKU (gradientLift laplacian u) := by
  let j : JetSpace U := ⟨actualJet χ hχ hc hs u, actualJet_mem χ hχ hc hs U hU hχU u⟩
  have hv : valueCLM U j = laplacianUpperGraphValue χ hχ hc hs (gradientLift laplacian u) := by
    change upperCutoffValueOperator χ hχ hc hs (formLift ⟨u, laplacian_domain_le u.property⟩) =
      upperCutoffHilbertValueOperator χ hχ hc hs (gradientEmbedding laplacian (gradientLift laplacian u))
    rw [gradientEmbedding_lift]
    exact (upperCutoffHilbertValueOperator_formEmbedding χ hχ hc hs
      (formLift ⟨u, laplacian_domain_le u.property⟩)).symm
  apply ContinuousMap.ext
  intro z
  change restriction U hU K hKU j z =
    laplacianUpperRepresentative χ hχ hc hs U hU hχU (gradientLift laplacian u) z
  apply restriction_eq_localRepresentative U hU K hKU z j hU (hKU z.property) Subset.rfl
    (laplacianUpperRepresentative_continuousOn χ hχ hc hs U hU hχU _)
  simpa only [hv] using
    laplacianUpperRepresentative_ae χ hχ hc hs U hU hχU (gradientLift laplacian u)

/-- Genuine norm-analytic weighted evaluation on every compact upper chart,
including seams, with no geometric regularity requirement on the compact set. -/
theorem exists_analytic_upperSchurEvaluation_on_plateau
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) {α : ℝ} (hα : 0 < α) :
    ∃ (E : ℂ → ModularHilbert →L[ℂ] C(K, ℂ)) (r : ℝ), 0 < r ∧
      AnalyticOnNhd ℂ E (Metric.ball 0 r) ∧
      ∀ κ : ℂ, ‖κ‖ < r → 0 < κ.re → ∀ f : ModularHilbert,
        ∃ hu : CuspSchur.actualSchurResolvent (parameter κ)
            (cuspWeightedInput α hα.le f) ∈ laplacian.domain,
          E κ f = laplacianUpperCompactRestriction χ hχ hc hs U hU hχU K hKU
            (gradientLift laplacian
              ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu⟩) := by
  obtain ⟨J, Q, r, hr, _hJ, hQ, hcoordinates⟩ :=
    exists_analytic_continuedJet χ hχ hc hs U hU hχU hα
  let R := restriction U hU K hKU
  let E : ℂ → ModularHilbert →L[ℂ] C(K, ℂ) := fun κ => R.comp (Q κ)
  have hE : AnalyticOnNhd ℂ E (Metric.ball 0 r) := by
    intro κ hκ
    exact ((ContinuousLinearMap.compL ℂ ModularHilbert (JetSpace U) C(K, ℂ) R).analyticAt _).comp
      (hQ κ hκ)
  refine ⟨E, r, hr, hE, ?_⟩
  intro κ hn hp f
  obtain ⟨hsub, hphysical⟩ := hcoordinates κ hn
  obtain ⟨hu, hj⟩ := hphysical hp f
  let u : laplacian.domain :=
    ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu⟩
  have hq : Q κ f = ⟨actualJet χ hχ hc hs u, actualJet_mem χ hχ hc hs U hU hχU u⟩ := by
    apply Subtype.ext
    have he := congrArg (fun A : ModularHilbert →L[ℂ] Jet => A f) hsub
    exact he.trans hj
  refine ⟨hu, ?_⟩
  change R (Q κ f) = _
  rw [hq]
  exact actualJet_restriction χ hχ hc hs U hU hχU K hKU u

/-- The chart and its cutoff are constructed from the actual compact upper set. -/
theorem exists_analytic_upperSchurEvaluation (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) {α : ℝ} (hα : 0 < α) :
    ∃ (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
      (hs : tsupport χ ⊆ upperHalfPlaneSet) (U : Set ℂ) (hU : IsOpen U)
      (hχU : EqOn χ (fun _ => 1) U) (hKU : K ⊆ U)
      (E : ℂ → ModularHilbert →L[ℂ] C(K, ℂ)) (r : ℝ), 0 < r ∧
      AnalyticOnNhd ℂ E (Metric.ball 0 r) ∧
      ∀ κ : ℂ, ‖κ‖ < r → 0 < κ.re → ∀ f : ModularHilbert,
        ∃ hu : CuspSchur.actualSchurResolvent (parameter κ)
            (cuspWeightedInput α hα.le f) ∈ laplacian.domain,
          E κ f = laplacianUpperCompactRestriction χ hχ hc hs U hU hχU K hKU
            (gradientLift laplacian
              ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu⟩) := by
  obtain ⟨L, U, χ, _hL, _hreg, hKL, hU, hLU, _hUc, _hUH, hχ, hc, hs, hχU⟩ :=
    exists_upperEvaluationCutoff (isCompact_iff_compactSpace.mpr inferInstance) hKH
  have hKU : K ⊆ U := hKL.trans (interior_subset.trans hLU)
  obtain ⟨E, r, hr, hE, hphysical⟩ :=
    exists_analytic_upperSchurEvaluation_on_plateau χ hχ hc hs U hU hχU K hKU hα
  exact ⟨χ, hχ, hc, hs, U, hU, hχU, hKU, E, r, hr, hE, hphysical⟩

end GapFamily.Analytic.UpperWeightedJet
