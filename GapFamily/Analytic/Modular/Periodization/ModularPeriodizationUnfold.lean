import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationIntegrable
import GapFamily.Analytic.Modular.Geometry.ModularTileIntegral

/-! Normalized unfolding for the actual modular periodization of compact seeds
supported anywhere in the upper half-plane, including across the seams. -/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff MatrixGroups

/-- The true full-matrix-group periodization unfolds with no residual factor. -/
theorem integral_modularPeriodization_upper {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    (∫ τ : UpperHalfPlane, modularPeriodization ψ τ ∂modularMeasure) =
      ∫ τ : UpperHalfPlane, ψ τ ∂volume := by
  simp_rw [modularPeriodization_coe]
  rw [integral_const_mul,
    integral_modularAction_tsum_eq_two_mul (upperSeed_integrable hψ.continuous hc hs)]
  ring

/-- Both sides are ordinary convergent integrals of the actual functions. -/
theorem modularPeriodization_upper_unfolding {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun τ : UpperHalfPlane => ψ τ) volume ∧
    Integrable (fun τ : UpperHalfPlane => modularPeriodization ψ τ) modularMeasure ∧
    (∫ τ : UpperHalfPlane, modularPeriodization ψ τ ∂modularMeasure) =
      ∫ τ : UpperHalfPlane, ψ τ ∂volume :=
  ⟨upperSeed_integrable hψ.continuous hc hs,
    modularPeriodization_upper_integrable hψ hc hs,
    integral_modularPeriodization_upper hψ hc hs⟩

end GapFamily.Analytic
