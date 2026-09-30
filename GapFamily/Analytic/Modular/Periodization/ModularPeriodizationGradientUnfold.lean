import GapFamily.Analytic.Modular.ModularGradientPairingIntegral
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationGradientSum

/-! Actual mixed gradient unfolding across arbitrary modular seams. -/
noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups

/-- The actual Hilbert gradient pairing unfolds to the ordinary hyperbolic
integral of the compact seed's mixed frame derivatives. -/
theorem inner_coreGradient_periodizedUpperCore (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    inner ℂ (coreGradient F) (coreGradient (periodizedUpperCore ψ hψ hc hs)) =
      ∫ τ : UpperHalfPlane, modularMixedFramePairing F.val ψ τ ∂volume := by
  rw [inner_coreGradient_eq_integral_mixedFramePairing]
  calc
    _ = ∫ τ : UpperHalfPlane, (1 / 2 : ℂ) *
        ∑' γ : SL(2, ℤ), modularMixedFramePairing F.val ψ (γ • τ) ∂modularMeasure := by
      apply integral_congr_ae
      filter_upwards with τ
      exact directionalMixedGradient_modularPeriodization F hψ hc hs τ
    _ = (1 / 2 : ℂ) * ((2 : ℂ) *
        ∫ τ : UpperHalfPlane, modularMixedFramePairing F.val ψ τ ∂volume) := by
      rw [integral_const_mul, integral_modularAction_tsum_eq_two_mul
        (modularMixedFramePairing_upper_integrable F hψ hc hs)]
    _ = _ := by ring

/-- Complete convergence and actual core gradient-pairing statement;
the compact test may cross vertical, circular, and elliptic seams. -/
theorem gradient_pairing_modularPeriodization_upper (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (modularMixedFramePairing F.val ψ) volume ∧
    Integrable (modularMixedFramePairing F.val
      (periodizedUpperCore ψ hψ hc hs).val) modularMeasure ∧
    inner ℂ (coreGradient F) (coreGradient (periodizedUpperCore ψ hψ hc hs)) =
      ∫ τ : UpperHalfPlane, modularMixedFramePairing F.val ψ τ ∂volume :=
  ⟨modularMixedFramePairing_upper_integrable F hψ hc hs,
    modularMixedFramePairing_core_integrable F (periodizedUpperCore ψ hψ hc hs),
    inner_coreGradient_periodizedUpperCore F hψ hc hs⟩

end GapFamily.Analytic
