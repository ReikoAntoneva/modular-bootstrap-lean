import GapFamily.Analytic.Modular.ModularContinuousTestPairing
import GapFamily.Analytic.Modular.ModularCompletedGreenTest
import GapFamily.Analytic.Modular.ModularClosedWeakDomain

/-! A genuine ordinary compact-test weak equation between continuous modular
representatives places a completed form vector in the actual Laplacian domain. -/

noncomputable section
namespace GapFamily.Analytic.ModularContinuousWeakDomain
open Set Filter MeasureTheory UpperHalfPlane ModularGradient LaplacianCovariance PoincareWeak
open scoped ContDiff MatrixGroups Topology

/-- Completed-form membership and an ordinary whole-upper-plane weak equation
suffice. Representative regularity is only continuity; no classical output
gradient, operator-domain witness, or density premise is supplied. -/
theorem exists_laplacian_value_of_continuous_weak (u : FormDomain) (G : ModularHilbert)
    (f g : ℂ → ℂ) (hf : ContinuousOn f upperHalfPlaneSet) (hg : ContinuousOn g upperHalfPlaneSet)
    (hfmod : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, f (γ • τ : UpperHalfPlane) = f τ)
    (hgmod : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, g (γ • τ : UpperHalfPlane) = g τ)
    (hu : formEmbedding u =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => f τ))
    (hG : G =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => g τ))
    (hweak : ∀ (ψ : ℂ → ℂ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ upperHalfPlaneSet →
      (∫ τ : UpperHalfPlane, star (ordinaryHyperbolicLaplacian ψ τ) * f τ ∂volume) =
        ∫ τ : UpperHalfPlane, star (ψ τ) * g τ ∂volume) :
    ∃ hdom : formEmbedding u ∈ laplacian.domain,
      laplacian ⟨formEmbedding u, hdom⟩ = G := by
  apply ModularClosedWeakDomain.exists_laplacian_value_of_periodized_pairing u G
  intro ψ hψ hc hs
  rw [ModularCompletedGreenTest.periodized_test_form_green ψ hψ hc hs u,
    ModularContinuousTestPairing.inner_periodizedUpperCore_value
      (formEmbedding u) f hf hfmod hu (ordinaryHyperbolicLaplacian ψ)
      (ordinaryHyperbolicLaplacian_contDiff hψ)
      (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
      ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hs),
    ModularContinuousTestPairing.inner_periodizedUpperCore_value
      G g hg hgmod hG ψ hψ hc hs]
  exact hweak ψ hψ hc hs

end GapFamily.Analytic.ModularContinuousWeakDomain
