import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationUpper

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- A compact ordinary seed supported inside the upper half-plane is genuinely
integrable for its actual hyperbolic volume. -/
theorem upperSeed_integrable {ψ : ℂ → ℂ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun τ : UpperHalfPlane => ψ τ) volume := by
  have hK := compact_modular_support_preimage_of_upper_support hc hs
  have hsupport : tsupport (fun τ : UpperHalfPlane => ψ τ) ⊆
      UpperHalfPlane.coe ⁻¹' tsupport ψ := by
    apply closure_minimal
    · intro τ hτ
      exact subset_tsupport ψ hτ
    · exact hK.isClosed
  have hcs : HasCompactSupport (fun τ : UpperHalfPlane => ψ τ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hsupport
  exact (hψ.comp UpperHalfPlane.continuous_coe).integrable_of_hasCompactSupport hcs

/-- The actual half-normalized periodization is ordinarily integrable; this
uses its proved smooth-core membership, not a totalized integral convention. -/
theorem modularPeriodization_upper_integrable {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun τ : UpperHalfPlane => modularPeriodization ψ τ) modularMeasure := by
  have hcore := modularPeriodization_mem_smoothCore_of_upper_support hψ hc hs
  exact hcore.2.2.1.integrable (by norm_num)

end GapFamily.Analytic
