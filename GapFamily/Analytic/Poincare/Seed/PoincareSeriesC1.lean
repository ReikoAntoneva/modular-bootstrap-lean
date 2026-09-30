import GapFamily.Analytic.Poincare.Seed.PoincareSeriesDifferentiable
import GapFamily.Analytic.Poincare.PoincareTermRegularity

/-! Actual real C¹ regularity of the convergent zero-energy Poincare series. -/

noncomputable section
namespace GapFamily.Analytic.PoincareSeriesC1
open Set Filter UpperHalfPlane PoincareTermGradient
  PoincareSeriesDifferentiable PoincareTermRegularity
open scoped Topology

/-- The convergent series is genuinely C¹ at every upper-half-plane point.
The continuous derivative field is its locally uniformly convergent derivative series. -/
theorem contDiffAt_complexPoincareSeries (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (τ : UpperHalfPlane) :
    ContDiffAt ℝ 1
      (fun z : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z)) (τ : ℂ) := by
  obtain ⟨r, hr, hU, u, hu, hb⟩ := exists_local_fderiv_majorant J hs τ
  apply contDiffAt_one_iff.mpr
  refine ⟨fun z : ℂ => ∑' q : CuspCoset, fderiv ℝ (term J s q) z,
    Metric.ball (τ : ℂ) r, Metric.ball_mem_nhds (τ : ℂ) hr, ?_, ?_⟩
  · exact continuousOn_tsum
      (fun q => (continuousOn_fderiv_term J s q).mono hU) hu hb
  · intro z hz
    exact hasFDerivAt_complexPoincareSeries J hs ⟨z, hU hz⟩

/-- Real C¹ regularity on the entire open upper half-plane, with no seam exclusion. -/
theorem contDiffOn_complexPoincareSeries (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    ContDiffOn ℝ 1
      (fun z : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z))
      upperHalfPlaneSet := by
  apply isOpen_upperHalfPlaneSet.contDiffOn_iff.mpr
  intro z hz
  exact contDiffAt_complexPoincareSeries J hs ⟨z, hz⟩

/-- The ordinary derivative of the actual series is continuous throughout the upper half-plane. -/
theorem continuousOn_fderiv_complexPoincareSeries (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    ContinuousOn
      (fderiv ℝ (fun z : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z)))
      upperHalfPlaneSet :=
  (contDiffOn_complexPoincareSeries J hs).continuousOn_fderiv_of_isOpen
    isOpen_upperHalfPlaneSet (by norm_num)

end GapFamily.Analytic.PoincareSeriesC1
