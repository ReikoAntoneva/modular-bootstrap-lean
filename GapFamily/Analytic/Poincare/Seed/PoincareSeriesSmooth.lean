import GapFamily.Analytic.Elliptic.LocalSmoothSeries
import GapFamily.Analytic.Poincare.PoincareHigherMajorant
import GapFamily.Analytic.Poincare.PoincareTermRegularity

/-!
Actual spatial smoothness of the convergent zero-energy Poincare series.
The all-order compact majorant is proved for the literal quotient terms.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareSeriesSmooth
open Set Filter UpperHalfPlane PoincareTermGradient PoincareTermRegularity
  PoincareHigherComposition LocalSmoothSeries
open scoped Topology ContDiff

/-- At every upper point the actual Poincare series is real C∞.
No smooth representative or derivative majorant is assumed in the statement. -/
theorem contDiffAt_complexPoincareSeries (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (τ : UpperHalfPlane) :
    ContDiffAt ℝ ∞
      (fun z : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z)) (τ : ℂ) := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp
    (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hcU : Metric.closedBall (τ : ℂ) r ⊆ upperHalfPlaneSet :=
    (Metric.closedBall_subset_ball (half_lt_self hR)).trans hRU
  have hU : Metric.ball (τ : ℂ) r ⊆ upperHalfPlaneSet :=
    Metric.ball_subset_closedBall.trans hcU
  have hcont : ContinuousOn UpperHalfPlane.ofComplex upperHalfPlaneSet := by
    apply UpperHalfPlane.ofComplex.continuousOn.mono
    intro z hz
    simpa [UpperHalfPlane.ofComplex] using hz
  let K : Set UpperHalfPlane := UpperHalfPlane.ofComplex '' Metric.closedBall (τ : ℂ) r
  have hK : IsCompact K := (isCompact_closedBall (τ : ℂ) r).image_of_continuousOn
    (hcont.mono hcU)
  have hb : ∀ n : ℕ, ∃ b : CuspCoset → ℝ, Summable b ∧
      ∀ (q : CuspCoset) (z : ℂ), z ∈ Metric.ball (τ : ℂ) r →
        ‖iteratedFDeriv ℝ n (term J s q) z‖ ≤ b q := by
    intro n
    obtain ⟨b, hb, _hb0, hbound⟩ := exists_compact_iteratedFDeriv_majorant_fixed n J hs hK
    refine ⟨b, hb, ?_⟩
    intro q z hz
    have hzu : 0 < z.im := hU hz
    have hk : UpperHalfPlane.ofComplex z ∈ K :=
      mem_image_of_mem _ (Metric.ball_subset_closedBall hz)
    have h := hbound q (UpperHalfPlane.ofComplex z) hk
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hzu] using h
  choose b hb hbound using hb
  have hsum := contDiffOn_tsum_of_bounds Metric.isOpen_ball
    (convex_ball (τ : ℂ) r).isPreconnected (fun q => term J s q)
    (fun q => (contDiffOn_term (n := ∞) J s q).mono hU) b hb hbound
  have he : (fun z : ℂ => ∑' q : CuspCoset, term J s q z) =
      (fun z : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z)) := by
    funext z
    simp only [term_eq_complexPoincareTerm_ofComplex, complexPoincareSeries]
  rw [he] at hsum
  exact (Metric.isOpen_ball.contDiffOn_iff.mp hsum) (Metric.mem_ball_self hr)

/-- Real C∞ regularity on the entire open upper half-plane, including every modular seam. -/
theorem contDiffOn_complexPoincareSeries (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    ContDiffOn ℝ ∞
      (fun z : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z))
      upperHalfPlaneSet := by
  apply isOpen_upperHalfPlaneSet.contDiffOn_iff.mpr
  intro z hz
  exact contDiffAt_complexPoincareSeries J hs ⟨z, hz⟩

end GapFamily.Analytic.PoincareSeriesSmooth
