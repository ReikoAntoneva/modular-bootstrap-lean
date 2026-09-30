import GapFamily.Analytic.Poincare.PoincareHyperbolicIntegralSeries
import GapFamily.Analytic.Poincare.PoincareTermIntegralResidual
import GapFamily.Analytic.Elliptic.HyperbolicGreenTest

/-! Actual common-region weak equation for the convergent zero-energy cusp series. -/
noncomputable section
namespace GapFamily.Analytic.PoincareWeak
open Set MeasureTheory LaplacianCovariance
open scoped ContDiff

/-- All three ordinary integrals in the actual series weak equation are integrable. -/
theorem poincare_weak_equation_integrable (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun z : ℂ => star (ordinaryHyperbolicLaplacian ψ z) *
      complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z) / (z.im : ℂ) ^ 2) ∧
    Integrable (fun z : ℂ => star (ψ z) *
      complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z) / (z.im : ℂ) ^ 2) ∧
    Integrable (fun z : ℂ => star (ψ z) *
      complexPoincareSeries 0 J (s + 2) (UpperHalfPlane.ofComplex z) / (z.im : ℂ) ^ 2) := by
  refine ⟨integrable_hyperbolic_testSeries _ (ordinaryHyperbolicLaplacian_continuous hψ)
    (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
    ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hψU) J hs,
    integrable_hyperbolic_testSeries ψ hψ.continuous hc hψU J hs, ?_⟩
  apply integrable_hyperbolic_testSeries ψ hψ.continuous hc hψU J
  norm_num [Complex.add_re]
  linarith

/-- The genuine ordinary weak residual of the actual convergent Poincaré series.
Only individual smooth summands are differentiated; no second derivative of the
infinite sum, form-domain premise, or continued seed is assumed. -/
theorem integral_poincare_weak_equation (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    (∫ z : ℂ, star (ordinaryHyperbolicLaplacian ψ z) *
      complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z) / (z.im : ℂ) ^ 2) =
      s * (1 - s) * (∫ z : ℂ, star (ψ z) *
        complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z) / (z.im : ℂ) ^ 2) +
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * (∫ z : ℂ, star (ψ z) *
        complexPoincareSeries 0 J (s + 2) (UpperHalfPlane.ofComplex z) / (z.im : ℂ) ^ 2) := by
  have hshift : 1 < (s + 2).re := by norm_num [Complex.add_re]; linarith
  have hleft := hasSum_integral_hyperbolic_testTerm _
    (ordinaryHyperbolicLaplacian_continuous hψ)
    (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
    ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hψU) J hs
  have hright := ((hasSum_integral_hyperbolic_testTerm ψ hψ.continuous hc hψU J hs).mul_left
    (s * (1 - s))).add
      ((hasSum_integral_hyperbolic_testTerm ψ hψ.continuous hc hψU J hshift).mul_left
        ((2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2))
  apply hleft.unique
  apply hright.congr
  intro t
  symm
  apply Finset.sum_congr rfl
  intro q _
  dsimp only
  rw [PoincareGreen.integral_hyperbolic_green_test ψ hψ hc hψU
    (fun z : ℂ => complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q)
    (contDiffOn_complexPoincareTerm_zero J s q)]
  exact integral_hyperbolic_testTerm_residual ψ hψ.continuous hc hψU J s q

end GapFamily.Analytic.PoincareWeak
