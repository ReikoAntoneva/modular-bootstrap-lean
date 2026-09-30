import GapFamily.Analytic.Foundation.UpperWeightedEvaluationCoherence

/-! A canonical continuous threshold response from the proved weighted local evaluations. -/
noncomputable section
namespace GapFamily.Analytic.UpperWeightedCoherence
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology ContDiff

/-- This choice is made only from the actual proved construction of weighted evaluations. -/
def chosenEvaluation (α : ℝ) (hα : 0 < α) (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) : Evaluation α hα K :=
  Classical.choice (nonempty_evaluation K hKH hα)

/-- A bounded compact observation of the threshold weighted response. -/
def weightedThresholdOnCompact (α : ℝ) (hα : 0 < α) (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) : ModularHilbert →L[ℂ] C(K, ℂ) :=
  (chosenEvaluation α hα K hKH).family 0

theorem singleton_subset_upper (τ : UpperHalfPlane) :
    ({(τ : ℂ)} : Set ℂ) ⊆ upperHalfPlaneSet := by
  intro z hz
  have hz' : z = (τ : ℂ) := Set.mem_singleton_iff.mp hz
  change 0 < z.im
  rw [hz']
  exact τ.im_pos

/-- The canonical value uses singleton observation of a genuinely constructed
analytic weighted response; compact coherence removes every auxiliary choice. -/
def weightedThresholdValue (α : ℝ) (hα : 0 < α) (f : ModularHilbert)
    (τ : UpperHalfPlane) : ℂ :=
  weightedThresholdOnCompact α hα ({(τ : ℂ)} : Set ℂ) (singleton_subset_upper τ)
    f ⟨(τ : ℂ), Set.mem_singleton _⟩

/-- Every actual constructed compact evaluation gives this same pointwise threshold value. -/
theorem weightedThresholdValue_eq_evaluation {α : ℝ} (hα : 0 < α)
    {K : Set ℂ} [CompactSpace K] (D : Evaluation α hα K)
    (f : ModularHilbert) (τ : UpperHalfPlane) (hτ : (τ : ℂ) ∈ K) :
    weightedThresholdValue α hα f τ = D.family 0 f ⟨(τ : ℂ), hτ⟩ := by
  have hsub : ({(τ : ℂ)} : Set ℂ) ⊆ K := Set.singleton_subset_iff.mpr hτ
  have heq := evaluation_restrict_zero
    (chosenEvaluation α hα ({(τ : ℂ)} : Set ℂ) (singleton_subset_upper τ)) D hsub
  exact congrArg
    (fun A : ModularHilbert →L[ℂ] C(({(τ : ℂ)} : Set ℂ), ℂ) =>
      A f ⟨(τ : ℂ), Set.mem_singleton _⟩) heq

/-- In particular, the fixed chosen compact family is exactly the restriction
of the canonical threshold function, including at thin observation sets. -/
theorem weightedThresholdValue_eq_compact {α : ℝ} (hα : 0 < α)
    (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (f : ModularHilbert) (τ : UpperHalfPlane) (hτ : (τ : ℂ) ∈ K) :
    weightedThresholdValue α hα f τ = weightedThresholdOnCompact α hα K hKH f ⟨(τ : ℂ), hτ⟩ :=
  weightedThresholdValue_eq_evaluation hα (chosenEvaluation α hα K hKH) f τ hτ

/-- The point observation is a genuine bounded complex linear functional of the source. -/
def weightedThresholdEvaluation (α : ℝ) (hα : 0 < α) (τ : UpperHalfPlane) :
    ModularHilbert →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ (⟨(τ : ℂ), Set.mem_singleton _⟩ : ({(τ : ℂ)} : Set ℂ))).comp
    (weightedThresholdOnCompact α hα ({(τ : ℂ)} : Set ℂ) (singleton_subset_upper τ))

@[simp] theorem weightedThresholdEvaluation_apply (α : ℝ) (hα : 0 < α)
    (τ : UpperHalfPlane) (f : ModularHilbert) :
    weightedThresholdEvaluation α hα τ f = weightedThresholdValue α hα f τ := rfl

/-- Compact observations control the canonical threshold function uniformly by
one finite source norm bound. -/
theorem weightedThresholdValue_compact_bound {α : ℝ} (hα : 0 < α)
    (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ B : ℝ, 0 < B ∧ ∀ (f : ModularHilbert) (τ : UpperHalfPlane), (τ : ℂ) ∈ K →
      ‖weightedThresholdValue α hα f τ‖ ≤ B * ‖f‖ := by
  let T := weightedThresholdOnCompact α hα K hKH
  refine ⟨‖T‖ + 1, by positivity, ?_⟩
  intro f τ hτ
  rw [weightedThresholdValue_eq_compact hα K hKH f τ hτ]
  exact ((T f).norm_coe_le_norm ⟨(τ : ℂ), hτ⟩).trans ((T.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (by linarith : ‖T‖ ≤ ‖T‖ + 1) (norm_nonneg f)))

/-- Continuity comes from genuine compact-neighborhood continuous observations,
not from pointwise passage to a limit of a possibly unbounded global family. -/
theorem continuous_weightedThresholdValue (α : ℝ) (hα : 0 < α) (f : ModularHilbert) :
    Continuous (weightedThresholdValue α hα f) := by
  apply continuous_iff_continuousAt.mpr
  intro τ
  obtain ⟨L, U, hL, _hreg, hτL, _hU, hLU, _hUc, hUH⟩ :=
    exists_regularCompact_upperNeighborhood (K := ({(τ : ℂ)} : Set ℂ))
      isCompact_singleton (singleton_subset_upper τ)
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hLH : L ⊆ upperHalfPlaneSet := hLU.trans (subset_closure.trans hUH)
  let D := chosenEvaluation α hα L hLH
  have hτint : (τ : ℂ) ∈ interior L := hτL (Set.mem_singleton _)
  have hLn : L ∈ 𝓝 (τ : ℂ) :=
    mem_of_superset (isOpen_interior.mem_nhds hτint) interior_subset
  have hcont : ContinuousAt (localContinuousExtend (D.family 0 f)) (τ : ℂ) :=
    (continuousOn_localContinuousExtend (D.family 0 f)).continuousAt hLn
  have hcomp : ContinuousAt
      (fun ξ : UpperHalfPlane => localContinuousExtend (D.family 0 f) (ξ : ℂ)) τ :=
    hcont.comp UpperHalfPlane.continuous_coe.continuousAt
  have hnear : ∀ᶠ ξ : UpperHalfPlane in 𝓝 τ, (ξ : ℂ) ∈ L :=
    UpperHalfPlane.continuous_coe.continuousAt.eventually hLn
  have heq : weightedThresholdValue α hα f =ᶠ[𝓝 τ]
      (fun ξ : UpperHalfPlane => localContinuousExtend (D.family 0 f) (ξ : ℂ)) := by
    filter_upwards [hnear] with ξ hξ
    rw [localContinuousExtend_apply _ hξ]
    exact weightedThresholdValue_eq_evaluation hα D f ξ hξ
  exact hcomp.congr_of_eventuallyEq heq

end GapFamily.Analytic.UpperWeightedCoherence
