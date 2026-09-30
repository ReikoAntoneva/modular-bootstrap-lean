import GapFamily.Analytic.Poincare.Continuation.PoincareCompactLaplacianIntegral

noncomputable section
namespace GapFamily.Analytic.PoincareWeak
open Set MeasureTheory

/-- Actual norm convergence of the ordinary inverse-square-density term integrals. -/
theorem hasSum_integral_hyperbolic_testTerm (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun q : CuspCoset => ∫ z : ℂ,
      star (ψ z) * complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q /
        (z.im : ℂ) ^ 2)
      (∫ z : ℂ, star (ψ z) * complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z) /
        (z.im : ℂ) ^ 2) := by
  have h := hasSum_integral_testTerm (fun z => ψ z / (z.im : ℂ) ^ 2)
    (testDivideHeightSquare_continuous hψ hψU) (testDivideHeightSquare_hasCompactSupport hc)
    ((testDivideHeightSquare_tsupport_subset ψ).trans hψU) J hs
  simpa [testSeries, testTerm, div_mul_eq_mul_div] using h

end GapFamily.Analytic.PoincareWeak
