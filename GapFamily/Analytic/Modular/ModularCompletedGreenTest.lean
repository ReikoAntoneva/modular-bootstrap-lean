import GapFamily.Analytic.Modular.ModularCoreGreenTest
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore

/-! The compact Green identity extends to the completed form domain because
both sides are bounded Hilbert pairings. No chosen gradient representative is needed. -/

noncomputable section
namespace GapFamily.Analytic.ModularCompletedGreenTest
open Set MeasureTheory UpperHalfPlane ModularGradient LaplacianCovariance PoincareWeak
open scoped ContDiff Topology

/-- Actual completed-form energy against a compact periodized test equals the
Hilbert value pairing with the periodized ordinary hyperbolic test Laplacian. -/
theorem periodized_test_form_green (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) (u : FormDomain) :
    inner ℂ (coreGradient (periodizedUpperCore ψ hψ hc hs)) (formGradient u) =
      inner ℂ (value (periodizedUpperCore (ordinaryHyperbolicLaplacian ψ)
        (ordinaryHyperbolicLaplacian_contDiff hψ)
        (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
        ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hs))) (formEmbedding u) := by
  refine coreForm_denseRange.induction_on u ?_ ?_
  · exact isClosed_eq (continuous_const.inner formGradient.continuous)
      (continuous_const.inner formEmbedding.continuous)
  · intro F
    rw [formGradient_coreForm, formEmbedding_coreForm,
      PoincareGreen.coreGradient_periodizedUpperCore_eq_hyperbolic_test F hψ hc hs,
      inner_periodizedUpperCore_value_eq_euclidean F
        (ordinaryHyperbolicLaplacian_contDiff hψ)
        (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
        ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hs)]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [upperSourceTestFunction, star_div₀, star_pow,
      Complex.star_def, Complex.conj_ofReal]
    ring

end GapFamily.Analytic.ModularCompletedGreenTest
