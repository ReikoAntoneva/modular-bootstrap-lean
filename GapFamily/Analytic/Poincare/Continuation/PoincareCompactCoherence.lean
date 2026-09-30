import GapFamily.Analytic.Poincare.Continuation.PoincareContinuationRegion
import GapFamily.Analytic.Poincare.Continuation.PoincareCompactContinuation
import Mathlib.Analysis.Analytic.Uniqueness

/-! Coherence from the actual convergent region of the full Poincaré series. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCanonical
open Set Filter UpperHalfPlane CuspFourierCutoff
open scoped Topology

/-- The common original-series region fixes the whole connected continuation region. -/
theorem eqOn_continuationRegion_of_common {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℝ} (hr : 0 < r)
    {f g : ℂ → E} (hf : AnalyticOnNhd ℂ f (continuationRegion r))
    (hg : AnalyticOnNhd ℂ g (continuationRegion r))
    (hcommon : ∀ κ : ℂ, (3 / 2 : ℝ) < κ.re → f κ = g κ) :
    EqOn f g (continuationRegion r) := by
  have htwo : (2 : ℂ) ∈ continuationRegion r := by
    right
    norm_num
  have hfg : f =ᶠ[𝓝 (2 : ℂ)] g := by
    have ho : IsOpen {κ : ℂ | (3 / 2 : ℝ) < κ.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have ht : (2 : ℂ) ∈ {κ : ℂ | (3 / 2 : ℝ) < κ.re} := by norm_num
    filter_upwards [ho.mem_nhds ht] with κ hκ
    exact hcommon κ hκ
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    (isPreconnected_continuationRegion hr) htwo hfg

/-- This data is inhabited by the proved compact Poincaré construction below.
Its complete common-region identity fixes the continuation, including at zero. -/
structure Continuation (K : Set ℂ) [CompactSpace K] where
  family : ℤ → ℂ → C(K, ℂ)
  radius : ℝ
  bound : ℝ
  radius_pos : 0 < radius
  radius_le_eighth : radius ≤ 1 / 8
  bound_pos : 0 < bound
  analytic_family : ∀ J : ℤ, AnalyticOnNhd ℂ (family J) (continuationRegion radius)
  uniform_bound : ∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ radius →
    ‖family J κ‖ ≤ bound * (1 + (J : ℝ) ^ 2)
  common_region : ∀ (J : ℤ) (κ : ℂ), (3 / 2 : ℝ) < κ.re → ∀ z : K,
    family J κ z = complexPoincareSeries 0 J (exponent κ) (ofComplex z)

/-- Every compact upper set has an actual continuation, with no certificate premise. -/
theorem nonempty_continuation (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) : Nonempty (Continuation K) := by
  obtain ⟨P, r, C, hr, hr8, hC, ha, hb, he⟩ :=
    PoincareCompactContinuation.exists_compactPoincareContinuation K hKH
  exact ⟨⟨P, r, C, hr, hr8, hC, ha, hb, he⟩⟩

variable {K₁ K₂ : Set ℂ} [CompactSpace K₁] [CompactSpace K₂]

/-- Restriction of any two actual compact continuations agrees throughout their
common connected parameter region, rather than only at the threshold. -/
theorem continuation_restrict_eqOn (D₁ : Continuation K₁) (D₂ : Continuation K₂)
    (h₁₂ : K₁ ⊆ K₂) (J : ℤ) :
    EqOn (D₁.family J)
      (fun κ => (D₂.family J κ).comp (ContinuousMap.inclusion h₁₂))
      (continuationRegion (min D₁.radius D₂.radius)) := by
  let R : C(K₂, ℂ) →L[ℂ] C(K₁, ℂ) :=
    ContinuousMap.compCLM ℂ ℂ (ContinuousMap.inclusion h₁₂)
  have ha : AnalyticOnNhd ℂ (D₁.family J)
      (continuationRegion (min D₁.radius D₂.radius)) :=
    (D₁.analytic_family J).mono (continuationRegion_mono (min_le_left _ _))
  have hb : AnalyticOnNhd ℂ (fun κ => R (D₂.family J κ))
      (continuationRegion (min D₁.radius D₂.radius)) := by
    intro κ hκ
    exact (R.analyticAt _).comp ((D₂.analytic_family J) κ
      (continuationRegion_mono (min_le_right _ _) hκ))
  apply eqOn_continuationRegion_of_common (lt_min D₁.radius_pos D₂.radius_pos) ha hb
  intro κ hκ
  apply ContinuousMap.ext
  intro z
  change D₁.family J κ z = D₂.family J κ ⟨z, h₁₂ z.property⟩
  rw [D₁.common_region J κ hκ z, D₂.common_region J κ hκ ⟨z, h₁₂ z.property⟩]

/-- The compact-family threshold value is independent of the chosen construction. -/
theorem continuation_restrict_zero (D₁ : Continuation K₁) (D₂ : Continuation K₂)
    (h₁₂ : K₁ ⊆ K₂) (J : ℤ) :
    D₁.family J 0 = (D₂.family J 0).comp (ContinuousMap.inclusion h₁₂) := by
  apply continuation_restrict_eqOn D₁ D₂ h₁₂ J
  left
  simpa only [Metric.mem_ball, dist_self] using lt_min D₁.radius_pos D₂.radius_pos

/-- The full C(K)-valued analytic germs are coherent under nested restriction. -/
theorem continuation_restrict_eventuallyEq (D₁ : Continuation K₁) (D₂ : Continuation K₂)
    (h₁₂ : K₁ ⊆ K₂) (J : ℤ) :
    D₁.family J =ᶠ[𝓝 (0 : ℂ)]
      (fun κ => (D₂.family J κ).comp (ContinuousMap.inclusion h₁₂)) := by
  have hz : (0 : ℂ) ∈ continuationRegion (min D₁.radius D₂.radius) := by
    left
    simpa only [Metric.mem_ball, dist_self] using lt_min D₁.radius_pos D₂.radius_pos
  filter_upwards [(isOpen_continuationRegion _).mem_nhds hz] with κ hκ
  exact continuation_restrict_eqOn D₁ D₂ h₁₂ J hκ

end GapFamily.Analytic.PoincareCanonical
