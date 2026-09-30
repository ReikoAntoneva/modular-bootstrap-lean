import GapFamily.Analytic.Modular.Elliptic.ModularEllipticH1
import GapFamily.Analytic.Elliptic.WeakLaplacianMollifier

noncomputable section
namespace GapFamily.Analytic.PoincareThresholdChartTest
open ModularGradient Homogenization
open scoped ContDiff

/-- The first real-coordinate chart derivative is the chart of the first derivative. -/
theorem ellipticChartTest_fderiv_one_fun (z : ℂ) {φ : (Fin 2 → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    (fun w => fderiv ℝ (ellipticChartTest z φ) w 1) =
      ellipticChartTest z (euclideanCoordDeriv 0 φ) := by
  funext w
  obtain ⟨v, rfl⟩ := (ellipticChart z).surjective w
  rw [ellipticChartTest_fderiv_one z hφ, ellipticChartTest_apply]
  rfl

/-- The second real-coordinate chart derivative is the chart of the second derivative. -/
theorem ellipticChartTest_fderiv_I_fun (z : ℂ) {φ : (Fin 2 → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    (fun w => fderiv ℝ (ellipticChartTest z φ) w Complex.I) =
      ellipticChartTest z (euclideanCoordDeriv 1 φ) := by
  funext w
  obtain ⟨v, rfl⟩ := (ellipticChart z).surjective w
  rw [ellipticChartTest_fderiv_I z hφ, ellipticChartTest_apply]
  rfl

/-- The real trace of chart second derivatives has no affine correction or scale factor. -/
theorem ellipticChartTest_second_trace (z : ℂ) {φ : (Fin 2 → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : Fin 2 → ℝ) :
    fderiv ℝ (fun w => fderiv ℝ (ellipticChartTest z φ) w 1) (ellipticChart z v) 1 +
        fderiv ℝ (fun w => fderiv ℝ (ellipticChartTest z φ) w Complex.I)
          (ellipticChart z v) Complex.I = euclideanCoordLaplacian φ v := by
  rw [ellipticChartTest_fderiv_one_fun z hφ, ellipticChartTest_fderiv_I_fun z hφ,
    ellipticChartTest_fderiv_one z (contDiff_euclideanCoordDeriv hφ 0),
    ellipticChartTest_fderiv_I z (contDiff_euclideanCoordDeriv hφ 1)]
  simp only [euclideanCoordLaplacian, Fin.sum_univ_two, euclideanCoordSecondDeriv]

/-- Casting a real smooth test to complex values commutes with the literal Laplacian. -/
theorem euclideanLaplacian_realTest (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (w : ℂ) :
    euclideanLaplacian (fun w => (ψ w : ℂ)) w =
      ((fderiv ℝ (fun t => fderiv ℝ ψ t 1) w 1 +
        fderiv ℝ (fun t => fderiv ℝ ψ t Complex.I) w Complex.I : ℝ) : ℂ) := by
  unfold euclideanLaplacian
  simp_rw [fderiv_realTest ψ hψ]
  rw [fderiv_realTest _ (contDiff_testDerivative ψ hψ 1),
    fderiv_realTest _ (contDiff_testDerivative ψ hψ Complex.I), Complex.ofReal_add]

/-- Exact affine transport of the complex-valued test Laplacian. -/
theorem euclideanLaplacian_ellipticChartTest (z : ℂ) {φ : (Fin 2 → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : Fin 2 → ℝ) :
    euclideanLaplacian (fun w => (ellipticChartTest z φ w : ℂ)) (ellipticChart z v) =
      (euclideanCoordLaplacian φ v : ℂ) := by
  rw [euclideanLaplacian_realTest _ (ellipticChartTest_contDiff z hφ),
    ellipticChartTest_second_trace z hφ]

end GapFamily.Analytic.PoincareThresholdChartTest
