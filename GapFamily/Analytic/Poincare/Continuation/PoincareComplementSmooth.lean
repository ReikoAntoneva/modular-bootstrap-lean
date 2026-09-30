import GapFamily.Analytic.Poincare.Continuation.PoincareComplementStrip
import GapFamily.Analytic.Poincare.PoincareModularSmoothTransport
import GapFamily.Analytic.Poincare.Seed.PoincareSeriesSmooth
import GapFamily.Analytic.Geometry.LaplacianSeedRepresentative

noncomputable section
namespace GapFamily.Analytic.PoincareComplement
open Set UpperHalfPlane
open scoped ContDiff

/-- The actual complement is smooth on the whole half-height strip by the
proved series regularity and the literal open-strip subtraction identity. -/
theorem contDiffOn_series_halfHeight (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    ContDiffOn ℝ ∞ (fun z : ℂ => series J s (UpperHalfPlane.ofComplex z))
      {z : ℂ | (1 / 2 : ℝ) < z.im} := by
  have hU : {z : ℂ | (1 / 2 : ℝ) < z.im} ⊆ upperHalfPlaneSet := by
    intro z hz
    change 0 < z.im
    change (1 / 2 : ℝ) < z.im at hz
    linarith
  have hP := (PoincareSeriesSmooth.contDiffOn_complexPoincareSeries J hs).mono hU
  have hχ : ContDiff ℝ ∞ (fun z : ℂ => (CuspFourierCutoff.cutoff z.im : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (CuspFourierCutoff.contDiff_cutoff.comp Complex.imCLM.contDiff)
  have hseed := (LaplacianCovariance.contDiffOn_zeroEnergySeed J s).mono hU
  apply (hP.sub (hχ.contDiffOn.mul hseed)).congr
  intro z hz
  have hy : 0 < z.im := hU hz
  have hseedEq : complexPointSeed 0 J s (UpperHalfPlane.ofComplex z) =
      LaplacianCovariance.zeroEnergySeed J s z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hy]
    exact (LaplacianCovariance.zeroEnergySeed_coe J s (⟨z, hy⟩ : UpperHalfPlane)).symm
  rw [series_ofComplex_eq_residual_of_half_lt_im J hs hz, hseedEq]

/-- Actual automorphy transports the proved strip regularity to all of H,
including modular seams, without all-order cutoff-series estimates. -/
theorem contDiffOn_series (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    ContDiffOn ℝ ∞ (fun z : ℂ => series J s (UpperHalfPlane.ofComplex z))
      upperHalfPlaneSet :=
  contDiffOn_of_modularInvariant_of_halfHeight (series J s)
    (fun γ τ => series_smul J s τ γ) (contDiffOn_series_halfHeight J hs)

/-- The literal ambient complement is smooth near every upper-half-plane point. -/
theorem contDiffAt_series (J : ℤ) {s : ℂ} (hs : 1 < s.re) (τ : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (fun z : ℂ => series J s (UpperHalfPlane.ofComplex z)) τ :=
  (contDiffOn_series J hs).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

end GapFamily.Analytic.PoincareComplement
