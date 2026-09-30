import GapFamily.Analytic.Foundation.UpperWeightedThresholdValue
import GapFamily.Analytic.Modular.Elliptic.ModularUpperEvaluationModular

/-! Automorphy of the actual weighted threshold value in its observation point. -/

noncomputable section
namespace GapFamily.Analytic.UpperWeightedCoherence
open Set Filter MeasureTheory UpperHalfPlane ModularGradient Dirichlet CuspSchurLocal
open scoped Topology ContDiff MatrixGroups

/-- Physical scalar observation equality determines the threshold observation. -/
theorem evaluation_zero_eq_of_physical_point_eq
    {α : ℝ} {hα : 0 < α} {K₁ K₂ : Set ℂ}
    [CompactSpace K₁] [CompactSpace K₂]
    (D₁ : Evaluation α hα K₁) (D₂ : Evaluation α hα K₂)
    (f : ModularHilbert) (p₁ : K₁) (p₂ : K₂)
    (hphysical : ∃ ε : ℝ, 0 < ε ∧ ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re →
      D₁.family κ f p₁ = D₂.family κ f p₂) :
    D₁.family 0 f p₁ = D₂.family 0 f p₂ := by
  have h₁ : AnalyticAt ℂ (fun κ => D₁.family κ f p₁) 0 :=
    ((ContinuousMap.evalCLM ℂ p₁ : C(K₁, ℂ) →L[ℂ] ℂ).analyticAt _).comp
      (((ContinuousLinearMap.apply ℂ C(K₁, ℂ) f).analyticAt _).comp D₁.analyticAt_zero)
  have h₂ : AnalyticAt ℂ (fun κ => D₂.family κ f p₂) 0 :=
    ((ContinuousMap.evalCLM ℂ p₂ : C(K₂, ℂ) →L[ℂ] ℂ).analyticAt _).comp
      (((ContinuousLinearMap.apply ℂ C(K₂, ℂ) f).analyticAt _).comp D₂.analyticAt_zero)
  exact (CuspSchurCoherence.analyticAt_eventuallyEq_of_physical h₁ h₂ hphysical).self_of_nhds

/-- Constructed compact threshold observations agree at modularly equivalent
points, by the actual physical graph identity and analytic continuation. -/
theorem evaluation_modular_zero
    {α : ℝ} {hα : 0 < α} {K₁ K₂ : Set ℂ}
    [CompactSpace K₁] [CompactSpace K₂]
    (D₁ : Evaluation α hα K₁) (D₂ : Evaluation α hα K₂)
    (f : ModularHilbert) (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (hτ₁ : ((γ • τ : UpperHalfPlane) : ℂ) ∈ K₁) (hτ₂ : (τ : ℂ) ∈ K₂) :
    D₁.family 0 f ⟨((γ • τ : UpperHalfPlane) : ℂ), hτ₁⟩ =
      D₂.family 0 f ⟨(τ : ℂ), hτ₂⟩ := by
  apply evaluation_zero_eq_of_physical_point_eq D₁ D₂ f
  refine ⟨min D₁.radius D₂.radius, lt_min D₁.radius_pos D₂.radius_pos, ?_⟩
  intro κ hn hp
  obtain ⟨hu₁, he₁⟩ := D₁.physical κ (hn.trans_le (min_le_left _ _)) hp f
  obtain ⟨hu₂, he₂⟩ := D₂.physical κ (hn.trans_le (min_le_right _ _)) hp f
  rw [he₁, he₂]
  exact laplacianUpperCompactEvaluation_modular
    D₁.cutoff D₁.cutoff_smooth D₁.cutoff_compact D₁.cutoff_support
    D₂.cutoff D₂.cutoff_smooth D₂.cutoff_compact D₂.cutoff_support
    D₁.region D₂.region D₁.open_region D₂.open_region D₁.one_region D₂.one_region
    K₁ K₂ D₁.compact_subset D₂.compact_subset
    (gradientLift laplacian
      ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu₁⟩)
    γ τ hτ₁ hτ₂

/-- The canonical actual threshold response is modular in its target point,
for every weighted Hilbert source. -/
theorem weightedThresholdValue_modular (α : ℝ) (hα : 0 < α)
    (f : ModularHilbert) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    weightedThresholdValue α hα f (γ • τ) = weightedThresholdValue α hα f τ := by
  let D₁ := chosenEvaluation α hα ({((γ • τ : UpperHalfPlane) : ℂ)} : Set ℂ)
    (singleton_subset_upper (γ • τ))
  let D₂ := chosenEvaluation α hα ({(τ : ℂ)} : Set ℂ) (singleton_subset_upper τ)
  exact evaluation_modular_zero D₁ D₂ f γ τ (Set.mem_singleton _) (Set.mem_singleton _)

end GapFamily.Analytic.UpperWeightedCoherence
