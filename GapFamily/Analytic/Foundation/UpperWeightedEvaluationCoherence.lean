import GapFamily.Analytic.Foundation.UpperWeightedSchurEvaluation
import GapFamily.Analytic.Modular.Elliptic.ModularUpperEvaluationCoherence
import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurCoherence

/-!
# Coherence of actual weighted upper-half-plane evaluations

Evaluation data is constructed from the actual weighted Schur resolvent.
Its analytic germ is independent of cutoff and commutes with restriction
to every smaller compact upper observation set, including thin compact sets.
-/

noncomputable section

namespace GapFamily.Analytic.UpperWeightedCoherence

open Set Filter ModularGradient UpperHalfPlane CuspSchurLocal Dirichlet
open scoped ContDiff Topology

/-- Constructed local evaluation data together with its actual physical meaning. -/
structure Evaluation (α : ℝ) (hα : 0 < α) (K : Set ℂ) [CompactSpace K] where
  cutoff : ℂ → ℂ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ upperHalfPlaneSet
  region : Set ℂ
  open_region : IsOpen region
  one_region : EqOn cutoff (fun _ => 1) region
  compact_subset : K ⊆ region
  family : ℂ → ModularHilbert →L[ℂ] C(K, ℂ)
  radius : ℝ
  radius_pos : 0 < radius
  analytic_family : AnalyticOnNhd ℂ family (Metric.ball 0 radius)
  physical : ∀ κ : ℂ, ‖κ‖ < radius → 0 < κ.re → ∀ f : ModularHilbert,
    ∃ hu : CuspSchur.actualSchurResolvent (parameter κ)
        (cuspWeightedInput α hα.le f) ∈ laplacian.domain,
      family κ f = laplacianUpperCompactRestriction cutoff cutoff_smooth cutoff_compact
        cutoff_support region open_region one_region K compact_subset
        (gradientLift laplacian
          ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu⟩)

/-- Every compact upper observation set has evaluation data from the actual construction. -/
theorem nonempty_evaluation (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) {α : ℝ} (hα : 0 < α) :
    Nonempty (Evaluation α hα K) := by
  obtain ⟨χ, hχ, hc, hs, U, hU, hχU, hKU, E, r, hr, hE, hphysical⟩ :=
    UpperWeightedJet.exists_analytic_upperSchurEvaluation K hKH hα
  exact ⟨⟨χ, hχ, hc, hs, U, hU, hχU, hKU, E, r, hr, hE, hphysical⟩⟩

variable {α : ℝ} {hα : 0 < α}
variable {K₁ K₂ : Set ℂ} [CompactSpace K₁] [CompactSpace K₂]

theorem Evaluation.analyticAt_zero (D : Evaluation α hα K₁) :
    AnalyticAt ℂ D.family 0 :=
  D.analytic_family 0 (Metric.mem_ball_self D.radius_pos)

/-- The actual physical resolvent fixes the analytic evaluation germ on nested compact sets. -/
theorem evaluation_restrict_eventuallyEq (D₁ : Evaluation α hα K₁)
    (D₂ : Evaluation α hα K₂) (h₁₂ : K₁ ⊆ K₂) :
    D₁.family =ᶠ[𝓝 (0 : ℂ)]
      (fun κ => (ContinuousMap.compCLM ℂ ℂ (ContinuousMap.inclusion h₁₂)).comp
        (D₂.family κ)) := by
  let R : C(K₂, ℂ) →L[ℂ] C(K₁, ℂ) :=
    ContinuousMap.compCLM ℂ ℂ (ContinuousMap.inclusion h₁₂)
  have h₂ : AnalyticAt ℂ (fun κ => R.comp (D₂.family κ)) 0 :=
    ((ContinuousLinearMap.compL ℂ ModularHilbert C(K₂, ℂ) C(K₁, ℂ) R).analyticAt _).comp
      D₂.analyticAt_zero
  apply CuspSchurCoherence.analyticAt_eventuallyEq_of_physical D₁.analyticAt_zero h₂
  refine ⟨min D₁.radius D₂.radius, lt_min D₁.radius_pos D₂.radius_pos, ?_⟩
  intro κ hn hp
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨hu₁, he₁⟩ := D₁.physical κ (hn.trans_le (min_le_left _ _)) hp f
  obtain ⟨hu₂, he₂⟩ := D₂.physical κ (hn.trans_le (min_le_right _ _)) hp f
  have hcoh := laplacianUpperCompactRestriction_coherent
    D₁.cutoff D₁.cutoff_smooth D₁.cutoff_compact D₁.cutoff_support
    D₂.cutoff D₂.cutoff_smooth D₂.cutoff_compact D₂.cutoff_support
    D₁.region D₂.region D₁.open_region D₂.open_region D₁.one_region D₂.one_region
    K₁ K₂ h₁₂ D₁.compact_subset D₂.compact_subset
  change D₁.family κ f = R (D₂.family κ f)
  rw [he₁, he₂]
  exact congrArg
    (fun T => T (gradientLift laplacian
      ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu₁⟩)) hcoh

/-- Threshold evaluation commutes with restriction and has no cutoff dependence. -/
theorem evaluation_restrict_zero (D₁ : Evaluation α hα K₁)
    (D₂ : Evaluation α hα K₂) (h₁₂ : K₁ ⊆ K₂) :
    D₁.family 0 = (ContinuousMap.compCLM ℂ ℂ (ContinuousMap.inclusion h₁₂)).comp
      (D₂.family 0) :=
  (evaluation_restrict_eventuallyEq D₁ D₂ h₁₂).self_of_nhds

end GapFamily.Analytic.UpperWeightedCoherence
