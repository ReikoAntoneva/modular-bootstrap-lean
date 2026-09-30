import GapFamily.Analytic.Geometry.LaplacianSeedResidual

noncomputable section
namespace GapFamily.Analytic.PoincareComplement
open Set Filter UpperHalfPlane LaplacianCovariance
open scoped ContDiff Topology

/-- The ordinary hyperbolic Laplacian is additive under subtraction of local real C² fields. -/
theorem ordinaryHyperbolicLaplacian_sub {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    ordinaryHyperbolicLaplacian (f - g) z =
      ordinaryHyperbolicLaplacian f z - ordinaryHyperbolicLaplacian g z := by
  simp only [ordinaryHyperbolicLaplacian]
  rw [euclideanLaplacian_eq_mathlib (f := f - g) (hf.sub hg), euclideanLaplacian_eq_mathlib hf,
    euclideanLaplacian_eq_mathlib hg, hf.laplacian_sub hg, smul_sub]

/-- The literal cutoff seed agrees with its smooth Fourier representative near each point of H. -/
theorem cutoffPointSeed_germ (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    (fun z : ℂ => (CuspFourierCutoff.cutoff z.im : ℂ) * zeroEnergySeed J s z)
      =ᶠ[𝓝 (τ : ℂ)] (fun z : ℂ => (CuspFourierCutoff.cutoff z.im : ℂ) *
        complexPointSeed 0 J s (UpperHalfPlane.ofComplex z)) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz,
    zeroEnergySeed_coe J s (⟨z, hz⟩ : UpperHalfPlane)]

/-- No parameter restriction is needed for local smoothness of the actual cutoff seed. -/
theorem contDiffAt_cutoffPointSeed (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (fun z : ℂ => (CuspFourierCutoff.cutoff z.im : ℂ) *
      complexPointSeed 0 J s (UpperHalfPlane.ofComplex z)) τ := by
  have hcut : ContDiff ℝ ∞ (fun z : ℂ => (CuspFourierCutoff.cutoff z.im : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (CuspFourierCutoff.contDiff_cutoff.comp Complex.imCLM.contDiff)
  exact (hcut.contDiffAt.mul (contDiffAt_zeroEnergySeed J s τ.im_pos)).congr_of_eventuallyEq
    (cutoffPointSeed_germ J s τ).symm

/-- The durable coordinate residual is the ordinary Laplacian of the smooth cutoff representative. -/
theorem ordinaryHyperbolicLaplacian_cutoffZeroEnergySeed (J : ℤ) (s : ℂ)
    (τ : UpperHalfPlane) :
    ordinaryHyperbolicLaplacian
        (fun z : ℂ => (CuspFourierCutoff.cutoff z.im : ℂ) * zeroEnergySeed J s z) τ -
      s * (1 - s) * ((CuspFourierCutoff.cutoff τ.im : ℂ) * zeroEnergySeed J s τ) =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * (CuspFourierCutoff.cutoff τ.im : ℂ) *
          zeroEnergySeed J (s + 2) τ -
        CuspFourierCutoff.profile (s - 1 / 2) τ.im * cuspFourierMode J τ.re := by
  have hcut : ContDiff ℝ ∞ (fun z : ℂ => (CuspFourierCutoff.cutoff z.im : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (CuspFourierCutoff.contDiff_cutoff.comp Complex.imCLM.contDiff)
  have hf : ContDiffAt ℝ 2
      (fun z : ℂ => (CuspFourierCutoff.cutoff z.im : ℂ) * zeroEnergySeed J s z)
      (Complex.mk τ.re τ.im) :=
    (hcut.contDiffAt.mul (contDiffAt_zeroEnergySeed J s τ.im_pos)).of_le (by norm_num)
  have he : CuspFourierCutoff.exponent (s - 1 / 2) = s := by
    unfold CuspFourierCutoff.exponent
    ring
  change ordinaryHyperbolicLaplacian _ (Complex.mk τ.re τ.im) - _ = _
  rw [ordinaryHyperbolicLaplacian_eq_coordinate_deriv hf]
  simpa only [zeroEnergySeed, cuspFourierMode, CuspFourierCutoff.radial, he,
    Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_pow,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    mul_assoc] using
    CuspFourierCutoff.fourier_coordinate_residual J (s - 1 / 2) τ.re τ.im_pos

/-- The literal cutoff source has its exact ordinary shifted residual at every point of H.
The collar term has a negative sign here; subtracting the cutoff source reverses it. -/
theorem ordinaryHyperbolicLaplacian_cutoffPointSeed (J : ℤ) (s : ℂ)
    (τ : UpperHalfPlane) :
    ordinaryHyperbolicLaplacian
        (fun z : ℂ => (CuspFourierCutoff.cutoff z.im : ℂ) *
          complexPointSeed 0 J s (UpperHalfPlane.ofComplex z)) τ -
      s * (1 - s) * ((CuspFourierCutoff.cutoff τ.im : ℂ) * complexPointSeed 0 J s τ) =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * (CuspFourierCutoff.cutoff τ.im : ℂ) *
          complexPointSeed 0 J (s + 2) τ -
        CuspFourierCutoff.profile (s - 1 / 2) τ.im * cuspFourierMode J τ.re := by
  rw [← ordinaryHyperbolicLaplacian_congr_germ (cutoffPointSeed_germ J s τ)]
  simpa only [zeroEnergySeed_coe] using ordinaryHyperbolicLaplacian_cutoffZeroEnergySeed J s τ

end GapFamily.Analytic.PoincareComplement
