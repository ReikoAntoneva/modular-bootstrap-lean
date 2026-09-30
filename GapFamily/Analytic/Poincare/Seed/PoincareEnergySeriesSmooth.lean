import GapFamily.Analytic.Elliptic.LocalSmoothSeries
import GapFamily.Analytic.Poincare.Seed.PoincareEnergySeedBasic
import GapFamily.Analytic.Poincare.Seed.PoincareEnergyHigher

/-!
Actual spatial smoothness of the normally convergent energy-difference Poincare series.
The complete derivative majorants and the smoothness of the literal quotient terms
are proved in the imported leaves; no such bound or regularity is assumed here.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergySeriesSmooth
open Set Filter UpperHalfPlane PoincareEnergySeedBasic
  PoincareEnergyHigher LocalSmoothSeries
open scoped Topology ContDiff

/-- The actual energy correction is real C∞ at every upper point whenever Re(s)>0,
for arbitrary complex energy and every integer spin. -/
theorem contDiffAt_complexPoincareEnergyDifference (E : ℂ) (J : ℤ) {s : ℂ}
    (hs : 0 < s.re) (τ : UpperHalfPlane) :
    ContDiffAt ℝ ∞
      (fun z : ℂ => complexPoincareEnergyDifference E J s (UpperHalfPlane.ofComplex z))
      (τ : ℂ) := by
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
        ‖iteratedFDeriv ℝ n
          (fun w : ℂ => complexPoincareDifferenceTerm E J s (UpperHalfPlane.ofComplex w) q)
          z‖ ≤ b q := by
    intro n
    obtain ⟨b, hb, _hb0, hbound⟩ :=
      exists_compact_iteratedFDeriv_difference_majorant n E J hs hK
    refine ⟨b, hb, ?_⟩
    intro q z hz
    have hzu : 0 < z.im := hU hz
    have hk : UpperHalfPlane.ofComplex z ∈ K :=
      mem_image_of_mem _ (Metric.ball_subset_closedBall hz)
    have h := hbound q (UpperHalfPlane.ofComplex z) hk
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hzu] using h
  choose b hb hbound using hb
  have hsum := contDiffOn_tsum_of_bounds Metric.isOpen_ball
    (convex_ball (τ : ℂ) r).isPreconnected
    (fun q z => complexPoincareDifferenceTerm E J s (UpperHalfPlane.ofComplex z) q)
    (fun q => (contDiffOn_complexPoincareDifferenceTerm (n := ∞) E J s q).mono hU)
    b hb hbound
  change ContDiffOn ℝ ∞
    (fun z : ℂ => complexPoincareEnergyDifference E J s (UpperHalfPlane.ofComplex z))
    (Metric.ball (τ : ℂ) r) at hsum
  exact (Metric.isOpen_ball.contDiffOn_iff.mp hsum) (Metric.mem_ball_self hr)

/-- Real C∞ regularity of the actual energy-difference series on the whole open
upper half-plane, including modular seams, for the full convergent range Re(s)>0. -/
theorem contDiffOn_complexPoincareEnergyDifference (E : ℂ) (J : ℤ) {s : ℂ}
    (hs : 0 < s.re) :
    ContDiffOn ℝ ∞
      (fun z : ℂ => complexPoincareEnergyDifference E J s (UpperHalfPlane.ofComplex z))
      upperHalfPlaneSet := by
  apply isOpen_upperHalfPlaneSet.contDiffOn_iff.mpr
  intro z hz
  exact contDiffAt_complexPoincareEnergyDifference E J hs ⟨z, hz⟩

end GapFamily.Analytic.PoincareEnergySeriesSmooth
