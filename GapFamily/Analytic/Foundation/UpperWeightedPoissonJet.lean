import GapFamily.Analytic.Foundation.UpperWeightedSchurField
import GapFamily.Analytic.Foundation.UpperPoissonActualJet
import GapFamily.Analytic.Cusp.Schur.CuspSchurNearThreshold

noncomputable section
namespace GapFamily.Analytic.UpperWeightedJet
open Set MeasureTheory ModularGradient UpperHalfPlane CuspSchurLocal
open UpperWeighted UpperSource LocalPoisson
open scoped ContDiff

private theorem analyticAt_prod_operator
    {E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    {F : ℂ → E →L[ℂ] A} {G : ℂ → E →L[ℂ] B}
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    AnalyticAt ℂ (fun κ => (F κ).prod (G κ)) 0 := by
  let P : ((E →L[ℂ] A) × (E →L[ℂ] B)) →L[ℂ] (E →L[ℂ] A × B) :=
    (ContinuousLinearMap.prodₗᵢ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  exact (P.analyticAt (F 0, G 0)).comp_of_eq (hF.prod hG) rfl

/-- Four actual upper-chart fields form a norm-analytic jet, whose physical
values are precisely the genuine domain solution's local Poisson data. -/
theorem exists_analytic_physicalJet
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) {α : ℝ} (hα : 0 < α) :
    ∃ J : ℂ → ModularHilbert →L[ℂ] Jet, AnalyticAt ℂ J 0 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re → ∀ f : ModularHilbert,
        ∃ hu : CuspSchur.actualSchurResolvent (parameter κ)
            (cuspWeightedInput α hα.le f) ∈ laplacian.domain,
          J κ f = actualJet χ hχ hc hs
            ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu⟩ := by
  obtain ⟨V, Dx, Dy, hV, hDx, hDy, hfields⟩ :=
    exists_analytic_upperWeightedSchur_fields χ hχ hc hs hα
  let ρ := upperSourceTestFunction χ
  have hρ : ContDiff ℝ ∞ ρ := contDiff_upperSourceTestFunction hχ hs
  have hcρ : HasCompactSupport ρ := hasCompactSupport_upperSourceTestFunction hc
  have hsρ : tsupport ρ ⊆ upperHalfPlaneSet :=
    (tsupport_upperSourceTestFunction_subset χ).trans hs
  obtain ⟨Vr, _, _, hVr, _, _, hrfields⟩ :=
    exists_analytic_upperWeightedSchur_fields ρ hρ hcρ hsρ hα
  let S : ℂ → ModularHilbert →L[ℂ] Field := fun κ =>
    (sourceOperator χ hχ hc hs).comp (cuspWeightedInput α hα.le) + parameter κ • Vr κ
  have hS : AnalyticAt ℂ S 0 :=
    analyticAt_const.add ((parameter_analyticAt 0).smul hVr)
  let J : ℂ → ModularHilbert →L[ℂ] Jet := fun κ =>
    (V κ).prod ((Dx κ).prod ((Dy κ).prod (S κ)))
  have hJ : AnalyticAt ℂ J 0 :=
    analyticAt_prod_operator hV (analyticAt_prod_operator hDx (analyticAt_prod_operator hDy hS))
  obtain ⟨ε, hε, hphysical⟩ := CuspSchur.exists_radius_actualSchur_inverse_physical
  refine ⟨J, hJ, min ε (1 / 2), lt_min hε (by norm_num), ?_⟩
  intro κ hnorm hκ f
  have hp : κ ≠ (1 / 2 : ℂ) := by
    have hn := hnorm.trans_le (min_le_right ε (1 / 2))
    intro he
    subst κ
    norm_num at hn
  obtain ⟨hu, hAu⟩ :=
    (hphysical κ (hnorm.trans_le (min_le_left _ _)) hκ).1 (cuspWeightedInput α hα.le f)
  let u : laplacian.domain :=
    ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu⟩
  have hform : formLift ⟨u, laplacian_domain_le u.property⟩ =
      CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f) := by
    apply formEmbedding_injective
    rfl
  have hA : laplacian u = cuspWeightedInput α hα.le f + parameter κ • (u : ModularHilbert) :=
    sub_eq_iff_eq_add.mp hAu
  have hVrphys : Vr κ f = sourceOperator χ hχ hc hs (u : ModularHilbert) := by
    change Vr κ f = sourceOperator χ hχ hc hs
      (CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f))
    rw [CuspSchur.actualSchurResolvent_apply]
    change Vr κ f = upperCutoffHilbertValueOperator ρ hρ hcρ hsρ
      (formEmbedding (CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f)))
    rw [upperCutoffHilbertValueOperator_formEmbedding]
    exact (hrfields κ hκ hp f).1
  refine ⟨hu, ?_⟩
  change (V κ f, (Dx κ f, (Dy κ f, S κ f))) = actualJet χ hχ hc hs u
  rw [actualJet, hform]
  apply Prod.ext (hfields κ hκ hp f).1
  apply Prod.ext (hfields κ hκ hp f).2.1
  apply Prod.ext (hfields κ hκ hp f).2.2
  change sourceOperator χ hχ hc hs (cuspWeightedInput α hα.le f) +
    parameter κ • Vr κ f = sourceOperator χ hχ hc hs (laplacian u)
  rw [hA, map_add, map_smul, hVrphys]

/-- The actual physical jet satisfies all local weak constraints on the open plateau. -/
theorem exists_analytic_physicalJet_mem
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    {α : ℝ} (hα : 0 < α) :
    ∃ J : ℂ → ModularHilbert →L[ℂ] Jet, AnalyticAt ℂ J 0 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re → ∀ f : ModularHilbert,
        J κ f ∈ jetSubmodule U ∧
          ∃ hu : CuspSchur.actualSchurResolvent (parameter κ)
              (cuspWeightedInput α hα.le f) ∈ laplacian.domain,
            J κ f = actualJet χ hχ hc hs
              ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu⟩ := by
  obtain ⟨J, hJ, ε, hε, hphysical⟩ := exists_analytic_physicalJet χ hχ hc hs hα
  refine ⟨J, hJ, ε, hε, fun κ hn hp f => ?_⟩
  obtain ⟨hu, heq⟩ := hphysical κ hn hp f
  exact ⟨heq.symm ▸ actualJet_mem χ hχ hc hs U hU hχU _, hu, heq⟩

end GapFamily.Analytic.UpperWeightedJet
