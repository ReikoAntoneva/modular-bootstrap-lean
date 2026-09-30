import GapFamily.Analytic.Poincare.PoincareTermGradient
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
Actual termwise real differentiation of the zero-energy Poincare series on the
open upper half-plane. The derivative series is genuinely norm summable.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareSeriesDifferentiable
open Set Filter UpperHalfPlane PoincareTermGradient
open scoped Topology

/-- A small ordinary open ball has one summable derivative bound. -/
theorem exists_local_fderiv_majorant (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (τ : UpperHalfPlane) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (τ : ℂ) r ⊆ upperHalfPlaneSet ∧
      ∃ u : CuspCoset → ℝ, Summable u ∧
        ∀ (q : CuspCoset) (z : ℂ), z ∈ Metric.ball (τ : ℂ) r →
          ‖fderiv ℝ (term J s q) z‖ ≤ u q := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp
    (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hcU : Metric.closedBall (τ : ℂ) r ⊆ upperHalfPlaneSet :=
    (Metric.closedBall_subset_ball hrR).trans hRU
  have hcont : ContinuousOn UpperHalfPlane.ofComplex upperHalfPlaneSet := by
    apply UpperHalfPlane.ofComplex.continuousOn.mono
    intro z hz
    simpa [UpperHalfPlane.ofComplex] using hz
  let K : Set UpperHalfPlane := UpperHalfPlane.ofComplex '' Metric.closedBall (τ : ℂ) r
  have hK : IsCompact K := (isCompact_closedBall (τ : ℂ) r).image_of_continuousOn
    (hcont.mono hcU)
  obtain ⟨u, hu, _hu0, hub⟩ := exists_compact_fderiv_majorant_fixed J hs hK
  refine ⟨r, hr, Metric.ball_subset_closedBall.trans hcU, u, hu, ?_⟩
  intro q z hz
  have hzu : 0 < z.im := hcU (Metric.ball_subset_closedBall hz)
  have hk : UpperHalfPlane.ofComplex z ∈ K :=
    mem_image_of_mem _ (Metric.ball_subset_closedBall hz)
  have hb := hub q (UpperHalfPlane.ofComplex z) hk
  simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hzu] using hb

/-- The actual derivative series converges absolutely at every upper point. -/
theorem summable_norm_fderiv_term (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (τ : UpperHalfPlane) :
    Summable (fun q : CuspCoset => ‖fderiv ℝ (term J s q) (τ : ℂ)‖) := by
  obtain ⟨r, hr, _hU, u, hu, hb⟩ := exists_local_fderiv_majorant J hs τ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => hb q τ (Metric.mem_ball_self hr)) hu

/-- Literal termwise differentiation of the actual quotient series.
The proof uses its established pointwise convergence, not a totalized divergent sum. -/
theorem hasFDerivAt_complexPoincareSeries (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (τ : UpperHalfPlane) :
    HasFDerivAt (fun z : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z))
      (∑' q : CuspCoset, fderiv ℝ (term J s q) (τ : ℂ)) (τ : ℂ) := by
  obtain ⟨r, hr, hU, u, hu, hb⟩ := exists_local_fderiv_majorant J hs τ
  have hf : ∀ (q : CuspCoset) (z : ℂ), z ∈ Metric.ball (τ : ℂ) r →
      HasFDerivAt (term J s q) (fderiv ℝ (term J s q) z) z := by
    intro q z hz
    exact (differentiableAt_term J s q ⟨z, hU hz⟩).hasFDerivAt
  have hs0 : Summable (fun q : CuspCoset => term J s q (τ : ℂ)) := by
    simpa only [term_apply] using (summable_norm_complexPoincareTerm 0 J hs τ).of_norm
  have hD := hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (τ : ℂ) r).isPreconnected hf hb (Metric.mem_ball_self hr) hs0
    (Metric.mem_ball_self hr)
  have he : (fun z : ℂ => ∑' q : CuspCoset, term J s q z) =
      (fun z : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z)) := by
    funext z
    simp only [term_eq_complexPoincareTerm_ofComplex, complexPoincareSeries]
  rw [he] at hD
  exact hD

/-- The ordinary real derivative is the convergent series of actual term derivatives. -/
theorem fderiv_complexPoincareSeries (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (τ : UpperHalfPlane) :
    fderiv ℝ (fun z : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z))
        (τ : ℂ) = ∑' q : CuspCoset, fderiv ℝ (term J s q) (τ : ℂ) :=
  (hasFDerivAt_complexPoincareSeries J hs τ).fderiv

end GapFamily.Analytic.PoincareSeriesDifferentiable
