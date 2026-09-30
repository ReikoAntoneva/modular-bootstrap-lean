import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperSmooth
import GapFamily.Analytic.Elliptic.GradientLocalIBP

/-!
# Ordinary weak differentiation of a genuine upper-half-plane cutoff

All integrals use ordinary area on the complex plane. The smooth cutoff
makes the core product globally smooth; compact complex tests can be placed
anywhere in the plane, without a support-containment premise.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

private theorem fderiv_star_complexTest (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (z v : ℂ) :
    fderiv ℝ (fun w => star (ψ w)) z v = star (fderiv ℝ ψ z v) := by
  have h := Complex.conjCLE.hasFDerivAt.comp z
    ((hψ.differentiable (by simp) z).hasFDerivAt)
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) h.fderiv

/-- Test-first ordinary weak derivative identity for the literal cutoff core
product, with its two actual product-rule terms. -/
theorem upperCutoff_core_weakDerivative (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (F : smoothCore) (v : ℂ) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) :
    (∫ z : ℂ, star (ψ z) *
      (χ z * fderiv ℝ F.val z v + fderiv ℝ χ z v * F.val z)) =
      -(∫ z : ℂ, star (fderiv ℝ ψ z v) * (χ z * F.val z)) := by
  have hp : ContDiff ℝ ∞ (fun z => χ z * F.val z) := upperCutoff_contDiff hχ hs F
  have hpc : HasCompactSupport (fun z => χ z * F.val z) := hc.mul_right
  have ht : ContDiff ℝ ∞ (fun z => star (ψ z)) := Complex.conjCLE.contDiff.comp hψ
  have htc : HasCompactSupport (fun z => star (ψ z)) := hcψ.comp_left (star_zero ℂ)
  have hd (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) :
      Continuous (fun z => fderiv ℝ f z v) :=
    (hf.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hleft : Integrable (fun z => fderiv ℝ (fun w => star (ψ w)) z v *
      (χ z * F.val z)) :=
    ((hd _ ht).mul hp.continuous).integrable_of_hasCompactSupport hpc.mul_left
  have hright : Integrable (fun z => star (ψ z) *
      fderiv ℝ (fun w => χ w * F.val w) z v) :=
    (ht.continuous.mul (hd _ hp)).integrable_of_hasCompactSupport htc.mul_right
  have hproduct : Integrable (fun z => star (ψ z) * (χ z * F.val z)) :=
    (ht.continuous.mul hp.continuous).integrable_of_hasCompactSupport htc.mul_right
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hleft hright hproduct
    (fun z _ => ht.differentiable (by simp) z)
    (fun z _ => hp.differentiable (by simp) z)
  simpa only [upperCutoff_fderiv_apply hχ hs, fderiv_star_complexTest ψ hψ, add_comm] using h

end GapFamily.Analytic.ModularGradient
