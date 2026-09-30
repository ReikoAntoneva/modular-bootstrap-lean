import GapFamily.Analytic.Poincare.Continuation.PoincareCompactCoherence

/-! A canonical continuous threshold seed from the proved compact continuations. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCanonical
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology ContDiff

/-- This choice uses only the actual proved construction of compact continuations. -/
def chosenContinuation (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) : Continuation K :=
  Classical.choice (nonempty_continuation K hKH)

/-- A continuous compact observation of the full threshold seed. -/
def thresholdSeedOnCompact (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) : C(K, ℂ) :=
  (chosenContinuation K hKH).family J 0

theorem singleton_subset_upper (τ : UpperHalfPlane) :
    ({(τ : ℂ)} : Set ℂ) ⊆ upperHalfPlaneSet := by
  intro z hz
  have hz' : z = (τ : ℂ) := Set.mem_singleton_iff.mp hz
  change 0 < z.im
  rw [hz']
  exact τ.im_pos

/-- Singleton observations define the canonical full threshold seed; compact
coherence removes the auxiliary compact set and constructed family. -/
def thresholdSeed (J : ℤ) (τ : UpperHalfPlane) : ℂ :=
  thresholdSeedOnCompact ({(τ : ℂ)} : Set ℂ) (singleton_subset_upper τ) J
    ⟨(τ : ℂ), Set.mem_singleton _⟩

/-- Every compact continuation gives the same pointwise threshold value. -/
theorem thresholdSeed_eq_continuation {K : Set ℂ} [CompactSpace K]
    (D : Continuation K) (J : ℤ) (τ : UpperHalfPlane) (hτ : (τ : ℂ) ∈ K) :
    thresholdSeed J τ = D.family J 0 ⟨(τ : ℂ), hτ⟩ := by
  have hsub : ({(τ : ℂ)} : Set ℂ) ⊆ K := Set.singleton_subset_iff.mpr hτ
  have heq := continuation_restrict_zero
    (chosenContinuation ({(τ : ℂ)} : Set ℂ) (singleton_subset_upper τ)) D hsub J
  exact congrArg
    (fun A : C(({(τ : ℂ)} : Set ℂ), ℂ) => A ⟨(τ : ℂ), Set.mem_singleton _⟩) heq

/-- The canonical seed restricts to the chosen compact observation, including
on compact sets with empty interior. -/
theorem thresholdSeed_eq_compact (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (τ : UpperHalfPlane)
    (hτ : (τ : ℂ) ∈ K) :
    thresholdSeed J τ = thresholdSeedOnCompact K hKH J ⟨(τ : ℂ), hτ⟩ :=
  thresholdSeed_eq_continuation (chosenContinuation K hKH) J τ hτ

/-- A genuine compact-family norm bound controls all integer seed indices. -/
theorem thresholdSeed_compact_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℤ) (τ : UpperHalfPlane), (τ : ℂ) ∈ K →
      ‖thresholdSeed J τ‖ ≤ C * (1 + (J : ℝ) ^ 2) := by
  let D := chosenContinuation K hKH
  refine ⟨D.bound, D.bound_pos, ?_⟩
  intro J τ hτ
  rw [thresholdSeed_eq_continuation D J τ hτ]
  exact ((D.family J 0).norm_coe_le_norm ⟨(τ : ℂ), hτ⟩).trans
    (D.uniform_bound J 0 (by simpa using D.radius_pos.le))

/-- Genuine compact-neighborhood observations give continuity of the canonical
threshold seed throughout the upper half-plane. -/
theorem continuous_thresholdSeed (J : ℤ) : Continuous (thresholdSeed J) := by
  apply continuous_iff_continuousAt.mpr
  intro τ
  obtain ⟨L, U, hL, _hreg, hτL, _hU, hLU, _hUc, hUH⟩ :=
    exists_regularCompact_upperNeighborhood (K := ({(τ : ℂ)} : Set ℂ))
      isCompact_singleton (singleton_subset_upper τ)
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hLH : L ⊆ upperHalfPlaneSet := hLU.trans (subset_closure.trans hUH)
  let D := chosenContinuation L hLH
  have hτint : (τ : ℂ) ∈ interior L := hτL (Set.mem_singleton _)
  have hLn : L ∈ 𝓝 (τ : ℂ) :=
    mem_of_superset (isOpen_interior.mem_nhds hτint) interior_subset
  have hcont : ContinuousAt (localContinuousExtend (D.family J 0)) (τ : ℂ) :=
    (continuousOn_localContinuousExtend (D.family J 0)).continuousAt hLn
  have hcomp : ContinuousAt
      (fun ξ : UpperHalfPlane => localContinuousExtend (D.family J 0) (ξ : ℂ)) τ :=
    hcont.comp UpperHalfPlane.continuous_coe.continuousAt
  have hnear : ∀ᶠ ξ : UpperHalfPlane in 𝓝 τ, (ξ : ℂ) ∈ L :=
    UpperHalfPlane.continuous_coe.continuousAt.eventually hLn
  have heq : thresholdSeed J =ᶠ[𝓝 τ]
      (fun ξ : UpperHalfPlane => localContinuousExtend (D.family J 0) (ξ : ℂ)) := by
    filter_upwards [hnear] with ξ hξ
    rw [localContinuousExtend_apply _ hξ]
    exact thresholdSeed_eq_continuation D J ξ hξ
  exact hcomp.congr_of_eventuallyEq heq

end GapFamily.Analytic.PoincareCanonical
