import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurGraph
import GapFamily.Analytic.Modular.Geometry.ModularCutoffEvaluation
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorLocalization

/-!
# Actual analytic local evaluation through the scalar threshold

The continued true cutoff graph is evaluated by the constructed bounded local
restriction map. On the physical side it agrees with evaluation of the actual
Schur inverse. A genuine smooth cutoff exists for every regular compact
interior observation set, so the final existence theorem has no cutoff premise.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal
open ModularGradient ModularGradient.InteriorCutoff Dirichlet Set
open scoped ContDiff

/-- Whenever the physical Schur response satisfies its actual operator equation,
the continued graph value is exactly the genuine smooth-cutoff graph lift. -/
theorem continuedCutoffGraph_apply_eq_physical
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ modularInterior)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ Real.exp L})
    {κ : ℂ} (hκ : 0 < κ.re) (f : ModularHilbert)
    (hu : CuspSchur.actualSchurResolvent (parameter κ)
      (modularLowCut (Real.exp T) f) ∈ laplacian.domain)
    (hAu : laplacian ⟨CuspSchur.actualSchurResolvent (parameter κ)
        (modularLowCut (Real.exp T) f), hu⟩ -
      parameter κ • CuspSchur.actualSchurResolvent (parameter κ)
        (modularLowCut (Real.exp T) f) = modularLowCut (Real.exp T) f) :
    continuedCutoffGraph χ hχ hc L T κ f =
      gradientLift laplacian (operatorCutoff χ hχ hc hs
        ⟨CuspSchur.actualSchurResolvent (parameter κ) (modularLowCut (Real.exp T) f), hu⟩) := by
  let u : laplacian.domain :=
    ⟨CuspSchur.actualSchurResolvent (parameter κ) (modularLowCut (Real.exp T) f), hu⟩
  rw [continuedCutoffGraph_apply,
    continuedCutoffSchur_eq_physical χ hχ hc hL hT hH hκ f,
    continuedCutoffLaplacian_eq_commutatorValue χ hχ hc hL hT hH hκ f hu hAu]
  change laplacianGraphPairMap (valueMultiplier χ hχ hc u, commutatorValue χ hχ hc u) =
    gradientLift laplacian (operatorCutoff χ hχ hc hs u)
  have hop : laplacian (operatorCutoff χ hχ hc hs u) = commutatorValue χ hχ hc u :=
    laplacian_formMultiplier χ hχ hc hs u
  rw [← operatorCutoff_value χ hχ hc hs u, ← hop]
  exact laplacianGraphPairMap_eq_of_mem (laplacian.mem_graph (operatorCutoff χ hχ hc hs u))


/-- The actual continuous local output, obtained from the genuine continued graph. -/
def continuedLocalEvaluation (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (L T : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] C(K, ℂ) :=
  (laplacianLocalRestriction K hKU hreg).comp (continuedCutoffGraph χ hχ hc L T κ)

/-- Analyticity is in the operator norm with genuine continuous-function outputs. -/
theorem continuedLocalEvaluation_analyticAt_zero (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (L T : ℝ) :
    AnalyticAt ℂ (continuedLocalEvaluation K hKU hreg χ hχ hc L T) 0 := by
  let Q : (ModularHilbert →L[ℂ] LaplacianGraphDomain) →L[ℂ]
      (ModularHilbert →L[ℂ] C(K, ℂ)) :=
    ContinuousLinearMap.compL ℂ ModularHilbert LaplacianGraphDomain C(K, ℂ)
      (laplacianLocalRestriction K hKU hreg)
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := ModularHilbert →L[ℂ] LaplacianGraphDomain)
    (F := ModularHilbert →L[ℂ] C(K, ℂ)) Q _).comp_of_eq
      (continuedCutoffGraph_analyticAt_zero χ hχ hc L T) rfl

/-- Each literal point gives an analytic bounded scalar functional of the source. -/
theorem continuedLocalEvaluation_point_analyticAt_zero (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (L T : ℝ) (x : K) :
    AnalyticAt ℂ (fun κ => (ContinuousMap.evalCLM ℂ x).comp
      (continuedLocalEvaluation K hKU hreg χ hχ hc L T κ)) 0 :=
  ((ContinuousLinearMap.compL ℂ ModularHilbert C(K, ℂ) ℂ
    (ContinuousMap.evalCLM ℂ x)).analyticAt _).comp_of_eq
      (continuedLocalEvaluation_analyticAt_zero K hKU hreg χ hχ hc L T) rfl

/-- Physical evaluation agrees with the actual Schur graph lift when the
actual operator equation holds; cutoff removal is a proved representative identity. -/
theorem continuedLocalEvaluation_apply_eq_physical (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ modularInterior) (hχK : EqOn χ (fun _ => 1) K)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ Real.exp L})
    {κ : ℂ} (hκ : 0 < κ.re) (f : ModularHilbert)
    (hu : CuspSchur.actualSchurResolvent (parameter κ)
      (modularLowCut (Real.exp T) f) ∈ laplacian.domain)
    (hAu : laplacian ⟨CuspSchur.actualSchurResolvent (parameter κ)
        (modularLowCut (Real.exp T) f), hu⟩ -
      parameter κ • CuspSchur.actualSchurResolvent (parameter κ)
        (modularLowCut (Real.exp T) f) = modularLowCut (Real.exp T) f) :
    continuedLocalEvaluation K hKU hreg χ hχ hc L T κ f =
      laplacianLocalRestriction K hKU hreg (gradientLift laplacian
        ⟨CuspSchur.actualSchurResolvent (parameter κ) (modularLowCut (Real.exp T) f), hu⟩) := by
  change laplacianLocalRestriction K hKU hreg (continuedCutoffGraph χ hχ hc L T κ f) = _
  rw [continuedCutoffGraph_apply_eq_physical χ hχ hc hs hL hT hH hκ f hu hAu]
  exact laplacianLocalRestriction_operatorCutoff K hKU hreg χ hχ hc hs hχK _

/-- One actual physical radius works for all Hilbert sources; the domain proof
comes from the proved near-threshold inverse theorem. -/
theorem exists_radius_continuedLocalEvaluation_eq_physical
    (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ modularInterior) (hχK : EqOn χ (fun _ => 1) K)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ Real.exp L}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re → ∀ f : ModularHilbert,
      ∃ hu : CuspSchur.actualSchurResolvent (parameter κ)
          (modularLowCut (Real.exp T) f) ∈ laplacian.domain,
        continuedLocalEvaluation K hKU hreg χ hχ hc L T κ f =
          laplacianLocalRestriction K hKU hreg (gradientLift laplacian
            ⟨CuspSchur.actualSchurResolvent (parameter κ) (modularLowCut (Real.exp T) f), hu⟩) := by
  obtain ⟨ε, hε, hphysical⟩ := CuspSchur.exists_radius_actualSchur_inverse_physical
  refine ⟨ε, hε, ?_⟩
  intro κ hnorm hκ f
  obtain ⟨hu, hAu⟩ := (hphysical κ hnorm hκ).1 (modularLowCut (Real.exp T) f)
  exact ⟨hu, continuedLocalEvaluation_apply_eq_physical K hKU hreg χ hχ hc hs hχK
    hL hT hH hκ f hu hAu⟩

/-- Every regular compact interior target and every finite source-height cap
admit an actual operator-norm analytic local evaluation continuation through zero.
No cutoff or physical equation is assumed in this final existence statement. -/
theorem exists_analytic_localSchurEvaluation (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ (E : ℂ → ModularHilbert →L[ℂ] C(K, ℂ)) (ε : ℝ),
      0 < ε ∧ AnalyticAt ℂ E 0 ∧
      ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re → ∀ f : ModularHilbert,
        ∃ hu : CuspSchur.actualSchurResolvent (parameter κ)
            (modularLowCut (Real.exp T) f) ∈ laplacian.domain,
          E κ f = laplacianLocalRestriction K hKU hreg (gradientLift laplacian
            ⟨CuspSchur.actualSchurResolvent (parameter κ) (modularLowCut (Real.exp T) f), hu⟩) := by
  obtain ⟨χ, V, L, hL, hχ, hc, hs, _hrange, _hV, hKV, _hVU, hχV, hH⟩ :=
    exists_modularInteriorCutoff (isCompact_iff_compactSpace.mpr inferInstance) hKU
  have hχK : EqOn χ (fun _ => 1) K := fun _ hz => hχV (subset_closure (hKV hz))
  obtain ⟨ε, hε, hphysical⟩ := exists_radius_continuedLocalEvaluation_eq_physical
    K hKU hreg χ hχ hc hs hχK hL hT hH
  exact ⟨continuedLocalEvaluation K hKU hreg χ hχ hc L T, ε, hε,
    continuedLocalEvaluation_analyticAt_zero K hKU hreg χ hχ hc L T, hphysical⟩

/-- The literal nondegenerate rectangle has such an actual analytic local
continuation with no supplied cutoff, uniformly for every source. -/
theorem exists_analytic_rectangleSchurEvaluation (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hK : localEvaluationRectangle a b c d ⊆ modularInterior)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ (E : ℂ → ModularHilbert →L[ℂ] C(localEvaluationRectangle a b c d, ℂ)) (ε : ℝ),
      0 < ε ∧ AnalyticAt ℂ E 0 ∧
      ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re → ∀ f : ModularHilbert,
        ∃ hu : CuspSchur.actualSchurResolvent (parameter κ)
            (modularLowCut (Real.exp T) f) ∈ laplacian.domain,
          E κ f = laplacianRectangleRestriction a b c d hab hcd hK (gradientLift laplacian
            ⟨CuspSchur.actualSchurResolvent (parameter κ) (modularLowCut (Real.exp T) f), hu⟩) :=
  exists_analytic_localSchurEvaluation _ hK (localEvaluationRectangle_regular hab hcd) hT

end GapFamily.Analytic.CuspSchurLocal
