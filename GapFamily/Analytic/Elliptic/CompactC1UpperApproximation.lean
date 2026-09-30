import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
namespace GapFamily.Analytic.CompactC1UpperApproximation

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology ContDiff Convolution Pointwise

private def shrinkingBump (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (δ / ((n : ℝ) + 1)) / 2
  rOut := δ / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hpos : 0 < δ / ((n : ℝ) + 1) := by positivity
    exact half_lt_self hpos

private theorem shrinkingBump_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (shrinkingBump δ hδ n).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump, mul_one_div, mul_zero] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ

private theorem norm_normed_convolution_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (φ : ContDiffBump (0 : ℂ))
    {g : ℂ → E} (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C)
    (z : ℂ) : ‖(φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z‖ ≤ C := by
  simpa only [dist_zero_right] using
    (dist_convolution_le (μ := (volume : Measure ℂ)) (g := g) (x₀ := z) (z₀ := 0)
      hC φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed
      hg.aestronglyMeasurable (fun x _ => by simpa using hb x))

private theorem scalar_precompR :
    (lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).precompR ℂ =
      (lsmul ℝ ℝ : ℝ →L[ℝ] (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ)) := by
  ext a b
  rfl

/-- A genuinely constructed smooth approximation with one compact upper-plane support,
pointwise convergence of values and derivative operators, and common global norm bounds. -/
theorem exists_compactC1UpperApproximation (ψ : ℂ → ℂ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ UpperHalfPlane.upperHalfPlaneSet ∧ tsupport ψ ⊆ K ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∃ ψn : ℕ → ℂ → ℂ,
        (∀ n, ContDiff ℝ ∞ (ψn n) ∧ tsupport (ψn n) ⊆ K) ∧
        (∀ z, Tendsto (fun n => ψn n z) atTop (𝓝 (ψ z))) ∧
        (∀ z, Tendsto (fun n => fderiv ℝ (ψn n) z) atTop (𝓝 (fderiv ℝ ψ z))) ∧
        (∀ n z, ‖ψn n z‖ ≤ C ∧ ‖fderiv ℝ (ψn n) z‖ ≤ C) := by
  obtain ⟨δ, hδ, hδH⟩ := hc.isCompact.exists_cthickening_subset_open
    UpperHalfPlane.isOpen_upperHalfPlaneSet hs
  let K : Set ℂ := cthickening δ (tsupport ψ)
  let φ : ℕ → ContDiffBump (0 : ℂ) := shrinkingBump δ hδ
  let ψn : ℕ → ℂ → ℂ := fun n => (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] ψ
  have hφlim : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    shrinkingBump_tendsto δ hδ
  have hφle (n : ℕ) : (φ n).rOut ≤ δ := by
    change δ / ((n : ℝ) + 1) ≤ δ
    exact div_le_self hδ.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hd (n : ℕ) (z : ℂ) : fderiv ℝ (ψn n) z =
      ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] fderiv ℝ ψ) z := by
    have hh := hc.hasFDerivAt_convolution_right (μ := (volume : Measure ℂ)) (lsmul ℝ ℝ)
      ((φ n).continuous_normed (μ := volume)).locallyIntegrable hψ z
    rw [scalar_precompR] at hh
    exact hh.fderiv
  have hD : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  obtain ⟨C₀, hC₀⟩ := hψ.continuous.bounded_above_of_compact_support hc
  obtain ⟨C₁, hC₁⟩ := hD.bounded_above_of_compact_support (hc.fderiv ℝ)
  let C : ℝ := max 0 (max C₀ C₁)
  have hC : 0 ≤ C := le_max_left _ _
  have hb₀ (z : ℂ) : ‖ψ z‖ ≤ C := (hC₀ z).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hb₁ (z : ℂ) : ‖fderiv ℝ ψ z‖ ≤ C :=
    (hC₁ z).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨K, hc.isCompact.cthickening, hδH, self_subset_cthickening _, C, hC,
    ψn, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨(φ n).hasCompactSupport_normed.contDiff_convolution_left
      (lsmul ℝ ℝ) (φ n).contDiff_normed hψ.continuous.locallyIntegrable, ?_⟩
    apply closure_minimal _ isClosed_cthickening
    intro z hz
    obtain ⟨a, ha, b, hb, hab⟩ := support_convolution_subset_swap (lsmul ℝ ℝ) hz
    have hb' : ‖b‖ ≤ δ := by
      have hball : b ∈ ball (0 : ℂ) (φ n).rOut := by
        simpa only [(φ n).support_normed_eq] using hb
      have hn : ‖b‖ < (φ n).rOut := by
        simpa only [mem_ball, dist_zero_right] using hball
      exact hn.le.trans (hφle n)
    apply mem_cthickening_of_dist_le z a δ (tsupport ψ) (subset_closure ha)
    rw [← hab]
    simpa only [dist_eq_norm, add_sub_cancel_left] using hb'
  · intro z
    exact ContDiffBump.convolution_tendsto_right_of_continuous hφlim hψ.continuous z
  · intro z
    simp_rw [hd]
    exact ContDiffBump.convolution_tendsto_right_of_continuous hφlim hD z
  · intro n z
    refine ⟨norm_normed_convolution_le (φ n) hψ.continuous hC hb₀ z, ?_⟩
    rw [hd]
    exact norm_normed_convolution_le (φ n) hD hC hb₁ z

end GapFamily.Analytic.CompactC1UpperApproximation
