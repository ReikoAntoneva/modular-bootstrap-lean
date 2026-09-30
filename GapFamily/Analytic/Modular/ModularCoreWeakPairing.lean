import GapFamily.Analytic.Modular.ModularCoreGreenTest
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore

noncomputable section
namespace GapFamily.Analytic.PoincareGreen
open Set MeasureTheory UpperHalfPlane ModularGradient LaplacianCovariance
open scoped ContDiff

/-- A literal second-order distribution equation between actual core functions
is exactly the form pairing against every genuine compact upper periodization. -/
theorem core_form_pairing_periodized_of_weak (F G : smoothCore)
    (hweak : ∀ (ψ : ℂ → ℂ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ upperHalfPlaneSet →
      (∫ z : ℂ, star (ordinaryHyperbolicLaplacian ψ z) * F.val z / (z.im : ℂ)^2) =
        ∫ z : ℂ, star (ψ z) * G.val z / (z.im : ℂ)^2)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    inner ℂ (formGradient (coreForm (periodizedUpperCore ψ hψ hc hs)))
      (formGradient (coreForm F)) =
      inner ℂ (formEmbedding (coreForm (periodizedUpperCore ψ hψ hc hs))) (value G) := by
  rw [formGradient_coreForm, formGradient_coreForm, formEmbedding_coreForm,
    coreGradient_periodizedUpperCore_eq_hyperbolic_test F hψ hc hs,
    hweak ψ hψ hc hs, inner_periodizedUpperCore_value_eq_euclidean G hψ hc hs]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [upperSourceTestFunction, star_div₀, star_pow,
    Complex.star_def, Complex.conj_ofReal]
  ring

end GapFamily.Analytic.PoincareGreen
