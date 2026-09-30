import GapFamily.Analytic.Poincare.Continuation.PoincareCompactIntegral
import GapFamily.Analytic.Poincare.PoincareLaplacianTest

noncomputable section
namespace GapFamily.Analytic.PoincareWeak
open Set MeasureTheory LaplacianCovariance
open scoped ContDiff

/-- Ordinary compact testing also applies to the actual hyperbolic Laplacian of a test. -/
theorem integral_laplacian_testSeries_eq_tsum (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    (∫ z : ℂ, testSeries (ordinaryHyperbolicLaplacian ψ) J s z) =
      ∑' q : CuspCoset, ∫ z : ℂ, testTerm (ordinaryHyperbolicLaplacian ψ) J s q z :=
  integral_testSeries_eq_tsum _ (ordinaryHyperbolicLaplacian_continuous hψ)
    (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
    ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hψU) J hs

theorem integrable_norm_tsum_laplacian_testTerm (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun z : ℂ => ∑' q : CuspCoset,
      ‖testTerm (ordinaryHyperbolicLaplacian ψ) J s q z‖) :=
  integrable_norm_tsum_testTerm _ (ordinaryHyperbolicLaplacian_continuous hψ)
    (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
    ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hψU) J hs

/-- The precise inverse-square measure factor is an ordinary compact-test multiplier. -/
theorem integral_hyperbolic_test_eq_tsum (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    (∫ z : ℂ, star (ψ z) * complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z) /
      (z.im : ℂ) ^ 2) =
      ∑' q : CuspCoset, ∫ z : ℂ,
        star (ψ z) * complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q /
          (z.im : ℂ) ^ 2 := by
  have h := integral_testSeries_eq_tsum (fun z => ψ z / (z.im : ℂ) ^ 2)
    (testDivideHeightSquare_continuous hψ hψU) (testDivideHeightSquare_hasCompactSupport hc)
    ((testDivideHeightSquare_tsupport_subset ψ).trans hψU) J hs
  simpa [testSeries, testTerm, div_mul_eq_mul_div] using h

theorem integrable_hyperbolic_testSeries (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun z : ℂ =>
      star (ψ z) * complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z) /
        (z.im : ℂ) ^ 2) := by
  have h := integrable_testSeries (fun z => ψ z / (z.im : ℂ) ^ 2)
    (testDivideHeightSquare_continuous hψ hψU) (testDivideHeightSquare_hasCompactSupport hc)
    ((testDivideHeightSquare_tsupport_subset ψ).trans hψU) J hs
  change Integrable (fun z : ℂ => star (ψ z / (z.im : ℂ) ^ 2) *
    complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z)) at h
  simpa [div_mul_eq_mul_div] using h

theorem integrable_norm_tsum_hyperbolic_testTerm (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun z : ℂ => ∑' q : CuspCoset,
      ‖star (ψ z) * complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q /
        (z.im : ℂ) ^ 2‖) := by
  have h := integrable_norm_tsum_testTerm (fun z => ψ z / (z.im : ℂ) ^ 2)
    (testDivideHeightSquare_continuous hψ hψU) (testDivideHeightSquare_hasCompactSupport hc)
    ((testDivideHeightSquare_tsupport_subset ψ).trans hψU) J hs
  simpa [testTerm, div_mul_eq_mul_div] using h

/-- The hyperbolic Laplacian test has the same actual inverse-square measure convention. -/
theorem integral_hyperbolic_laplacian_test_eq_tsum (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    (∫ z : ℂ, star (ordinaryHyperbolicLaplacian ψ z) *
      complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z) / (z.im : ℂ) ^ 2) =
      ∑' q : CuspCoset, ∫ z : ℂ, star (ordinaryHyperbolicLaplacian ψ z) *
        complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q / (z.im : ℂ) ^ 2 :=
  integral_hyperbolic_test_eq_tsum _ (ordinaryHyperbolicLaplacian_continuous hψ)
    (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
    ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hψU) J hs

/-- Shifted forcing is tested against exactly the same hyperbolic volume density. -/
theorem integral_shifted_hyperbolic_test_eq_tsum (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : -1 < s.re) :
    (∫ z : ℂ, star (ψ z) * complexPoincareSeries 0 J (s + 2) (UpperHalfPlane.ofComplex z) /
      (z.im : ℂ) ^ 2) =
      ∑' q : CuspCoset, ∫ z : ℂ,
        star (ψ z) * complexPoincareTerm 0 J (s + 2) (UpperHalfPlane.ofComplex z) q /
          (z.im : ℂ) ^ 2 := by
  apply integral_hyperbolic_test_eq_tsum ψ hψ hc hψU J
  norm_num [Complex.add_re]
  linarith

end GapFamily.Analytic.PoincareWeak
