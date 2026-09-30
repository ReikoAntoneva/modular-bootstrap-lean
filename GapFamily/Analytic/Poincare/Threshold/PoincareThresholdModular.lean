import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdValue

/-! Actual modular invariance of the canonical full threshold seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCanonical
open Set Filter UpperHalfPlane CuspFourierCutoff
open scoped Topology MatrixGroups

/-- The original series fixes the modular relation throughout the connected
parameter region of any compact observation containing both orbit points. -/
theorem continuation_orbit_eqOn {K : Set ℂ} [CompactSpace K] (D : Continuation K)
    (J : ℤ) (τ : UpperHalfPlane) (g : SL(2, ℤ))
    (hτ : (τ : ℂ) ∈ K) (hgτ : ((g • τ : UpperHalfPlane) : ℂ) ∈ K) :
    EqOn (fun κ => D.family J κ ⟨((g • τ : UpperHalfPlane) : ℂ), hgτ⟩)
      (fun κ => D.family J κ ⟨(τ : ℂ), hτ⟩) (continuationRegion D.radius) := by
  have ha : AnalyticOnNhd ℂ (fun κ => D.family J κ ⟨(τ : ℂ), hτ⟩)
      (continuationRegion D.radius) := by
    intro κ hκ
    exact ((ContinuousMap.evalCLM ℂ (⟨(τ : ℂ), hτ⟩ : K)).analyticAt _).comp
      (D.analytic_family J κ hκ)
  have hb : AnalyticOnNhd ℂ
      (fun κ => D.family J κ ⟨((g • τ : UpperHalfPlane) : ℂ), hgτ⟩)
      (continuationRegion D.radius) := by
    intro κ hκ
    exact ((ContinuousMap.evalCLM ℂ
      (⟨((g • τ : UpperHalfPlane) : ℂ), hgτ⟩ : K)).analyticAt _).comp
      (D.analytic_family J κ hκ)
  apply eqOn_continuationRegion_of_common D.radius_pos hb ha
  intro κ hκ
  rw [D.common_region J κ hκ, D.common_region J κ hκ]
  change complexPoincareSeries 0 J (exponent κ)
      (ofComplex ((g • τ : UpperHalfPlane) : ℂ)) =
    complexPoincareSeries 0 J (exponent κ) (ofComplex (τ : ℂ))
  rw [ofComplex_apply, ofComplex_apply]
  exact complexPoincareSeries_smul 0 J (exponent κ) τ g

/-- The canonical full zero-energy threshold seed is genuinely modular on H. -/
theorem thresholdSeed_smul (J : ℤ) (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    thresholdSeed J (g • τ) = thresholdSeed J τ := by
  let K : Set ℂ := {(τ : ℂ), ((g • τ : UpperHalfPlane) : ℂ)}
  have hK : IsCompact K := isCompact_singleton.insert _
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hKH : K ⊆ upperHalfPlaneSet := by
    intro z hz
    change 0 < z.im
    rcases hz with hz | hz
    · rw [hz]
      exact τ.im_pos
    · have he : z = ((g • τ : UpperHalfPlane) : ℂ) := Set.mem_singleton_iff.mp hz
      rw [he]
      exact (g • τ : UpperHalfPlane).im_pos
  let D := chosenContinuation K hKH
  have hτ : (τ : ℂ) ∈ K := Set.mem_insert _ _
  have hgτ : ((g • τ : UpperHalfPlane) : ℂ) ∈ K :=
    Set.mem_insert_of_mem _ (Set.mem_singleton _)
  rw [thresholdSeed_eq_continuation D J (g • τ) hgτ,
    thresholdSeed_eq_continuation D J τ hτ]
  apply continuation_orbit_eqOn D J τ g hτ hgτ
  left
  simpa only [Metric.mem_ball, dist_self] using D.radius_pos

end GapFamily.Analytic.PoincareCanonical
