import GapFamily.Analytic.Modular.Elliptic.ModularLocalDerivativeTest
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationGradientEuclidean

/-! Ordinary compact-test energy pairing for the actual completed form domain. -/
noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff Topology

/-- The core unfolding extends through actual form-core density to the completed form. -/
theorem formGradient_periodizedUpperCore_pairing
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (hχone : ∀ z ∈ tsupport ψ, χ z = 1)
    (u : FormDomain) :
    inner ℂ (formGradient u) (coreGradient (periodizedUpperCore ψ hψ hcψ hsψ)) =
      inner ℂ (upperCutoffGradientOperator χ hχ hcχ hsχ 1 u)
        (upperTestDerivativeL2 ψ hψ hcψ 1) +
      inner ℂ (upperCutoffGradientOperator χ hχ hcχ hsχ Complex.I u)
        (upperTestDerivativeL2 ψ hψ hcψ Complex.I) := by
  refine coreForm_denseRange.induction_on u ?_ ?_
  · exact isClosed_eq (formGradient.continuous.inner continuous_const)
      (((upperCutoffGradientOperator χ hχ hcχ hsχ 1).continuous.inner continuous_const).add
        ((upperCutoffGradientOperator χ hχ hcχ hsχ Complex.I).continuous.inner continuous_const))
  · intro F
    rw [formGradient_coreForm, inner_upperCutoffGradient_core_test χ hχ hcχ hsχ F ψ hψ hcψ hχone 1,
      inner_upperCutoffGradient_core_test χ hχ hcχ hsχ F ψ hψ hcψ hχone Complex.I,
      ← integral_add (upperCutoffGradient_core_test_integrable χ hχ hcχ hsχ F ψ hψ hcψ hχone 1)
        (upperCutoffGradient_core_test_integrable χ hχ hcχ hsχ F ψ hψ hcψ hχone Complex.I)]
    exact inner_coreGradient_periodizedUpperCore_eq_euclideanIntegral F hψ hcψ hsψ

/-- Test-first orientation of the actual completed energy pairing. -/
theorem periodizedUpperCore_formGradient_pairing
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (hχone : ∀ z ∈ tsupport ψ, χ z = 1)
    (u : FormDomain) :
    inner ℂ (coreGradient (periodizedUpperCore ψ hψ hcψ hsψ)) (formGradient u) =
      inner ℂ (upperTestDerivativeL2 ψ hψ hcψ 1)
        (upperCutoffGradientOperator χ hχ hcχ hsχ 1 u) +
      inner ℂ (upperTestDerivativeL2 ψ hψ hcψ Complex.I)
        (upperCutoffGradientOperator χ hχ hcχ hsχ Complex.I u) := by
  simpa only [map_add, inner_conj_symm] using congrArg (starRingEnd ℂ)
    (formGradient_periodizedUpperCore_pairing χ hχ hcχ hsχ ψ hψ hcψ hsψ hχone u)

/-- The genuine completed energy is an ordinary Euclidean integral of the actual local fields. -/
theorem periodizedUpperCore_formGradient_integral
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (hχone : ∀ z ∈ tsupport ψ, χ z = 1)
    (u : FormDomain) :
    inner ℂ (coreGradient (periodizedUpperCore ψ hψ hcψ hsψ)) (formGradient u) =
      ∫ z : ℂ, star (fderiv ℝ ψ z 1) * upperCutoffGradientOperator χ hχ hcχ hsχ 1 u z +
        star (fderiv ℝ ψ z Complex.I) * upperCutoffGradientOperator χ hχ hcχ hsχ Complex.I u z := by
  rw [periodizedUpperCore_formGradient_pairing χ hχ hcχ hsχ ψ hψ hcψ hsψ hχone u,
    inner_test_upperCutoffGradient_integral, inner_test_upperCutoffGradient_integral,
    ← integral_add (upperCutoffGradient_test_integrable χ hχ hcχ hsχ u ψ hψ hcψ 1)
      (upperCutoffGradient_test_integrable χ hχ hcχ hsχ u ψ hψ hcψ Complex.I)]

/-- Integrability is part of the ordinary completed-field test identity. -/
theorem periodizedUpperCore_formGradient_integrable
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (u : FormDomain) :
    Integrable (fun z : ℂ =>
      star (fderiv ℝ ψ z 1) * upperCutoffGradientOperator χ hχ hcχ hsχ 1 u z +
      star (fderiv ℝ ψ z Complex.I) * upperCutoffGradientOperator χ hχ hcχ hsχ Complex.I u z) volume :=
  (upperCutoffGradient_test_integrable χ hχ hcχ hsχ u ψ hψ hcψ 1).add
    (upperCutoffGradient_test_integrable χ hχ hcχ hsχ u ψ hψ hcψ Complex.I)

end GapFamily.Analytic
