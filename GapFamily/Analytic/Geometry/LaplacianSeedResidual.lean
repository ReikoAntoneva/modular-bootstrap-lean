import GapFamily.Analytic.Geometry.LaplacianMobiusCovariance
import GapFamily.Analytic.Geometry.LaplacianSeedRadial
import GapFamily.Analytic.Geometry.LaplacianSeedRepresentative

noncomputable section
namespace GapFamily.Analytic.LaplacianCovariance
open Filter UpperHalfPlane
open scoped Topology MatrixGroups ContDiff

/-- The ordinary second-order operator depends only on the actual local representative. -/
theorem ordinaryHyperbolicLaplacian_congr_germ {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) :
    ordinaryHyperbolicLaplacian f z = ordinaryHyperbolicLaplacian g z := by
  have hd := h.fderiv (𝕜 := ℝ)
  have hdv (v : ℂ) : (fun w => fderiv ℝ f w v) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ g w v) := hd.mono fun _ hw => congrArg (fun A => A v) hw
  simp only [ordinaryHyperbolicLaplacian, euclideanLaplacian,
    (hdv 1).fderiv_eq, (hdv Complex.I).fderiv_eq]

/-- The actual uncompleted direct seed has its exact shifted residual for every complex s. -/
theorem ordinaryHyperbolicLaplacian_zeroEnergySeed (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    ordinaryHyperbolicLaplacian (zeroEnergySeed J s) τ -
        s * (1 - s) * zeroEnergySeed J s τ =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * zeroEnergySeed J (s + 2) τ := by
  have hs : ContDiffAt ℝ 2 (zeroEnergySeed J s) (Complex.mk τ.re τ.im) :=
    (contDiffAt_zeroEnergySeed J s τ.im_pos).of_le (by norm_num)
  have hc := ordinaryHyperbolicLaplacian_eq_coordinate_deriv hs
  change ordinaryHyperbolicLaplacian (zeroEnergySeed J s) (Complex.mk τ.re τ.im) - _ = _
  rw [hc]
  simpa only [zeroEnergySeed, cuspFourierMode, Complex.real_smul,
    Complex.ofReal_neg, Complex.ofReal_pow, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    mul_assoc] using
    zeroEnergy_coordinate_residual J s τ.re τ.im_pos

/-- Covariance gives the same exact equation for each actual modular coset representative. -/
theorem ordinaryHyperbolicLaplacian_zeroEnergyRepresentative
    (J : ℤ) (s : ℂ) (q : CuspCoset) (τ : UpperHalfPlane) :
    ordinaryHyperbolicLaplacian (zeroEnergyRepresentative J s q) τ -
        s * (1 - s) * zeroEnergyRepresentative J s q τ =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * zeroEnergyRepresentative J (s + 2) q τ := by
  have hs : ContDiffAt ℝ 2 (zeroEnergySeed J s) (q.out • τ : UpperHalfPlane) :=
    (contDiffAt_zeroEnergySeed J s (q.out • τ : UpperHalfPlane).im_pos).of_le (by norm_num)
  simp only [zeroEnergyRepresentative, Function.comp_apply,
    ordinaryHyperbolicLaplacian_comp_rawModularAction q.out τ hs, rawModularAction_coe]
  exact ordinaryHyperbolicLaplacian_zeroEnergySeed J s (q.out • τ)

/-- The literal source quotient summand satisfies the ordinary hyperbolic equation.
No series differentiation, summability region, weak equation, or operator domain is asserted. -/
theorem ordinaryHyperbolicLaplacian_complexPoincareTerm_zero
    (J : ℤ) (s : ℂ) (q : CuspCoset) (τ : UpperHalfPlane) :
    ordinaryHyperbolicLaplacian
        (fun z : ℂ => complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q) τ -
        s * (1 - s) * complexPoincareTerm 0 J s τ q =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * complexPoincareTerm 0 J (s + 2) τ q := by
  rw [← ordinaryHyperbolicLaplacian_congr_germ (zeroEnergyRepresentative_germ J s q τ),
    ← zeroEnergyRepresentative_coe J s q τ, ← zeroEnergyRepresentative_coe J (s + 2) q τ]
  exact ordinaryHyperbolicLaplacian_zeroEnergyRepresentative J s q τ

end GapFamily.Analytic.LaplacianCovariance
