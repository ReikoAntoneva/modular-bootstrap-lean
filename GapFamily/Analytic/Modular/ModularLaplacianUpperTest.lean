import GapFamily.Analytic.Modular.ModularClosedTestPairing
import GapFamily.Analytic.Modular.ModularLaplacian

/-! Actual Laplacian-domain energy tested across modular seams.
The source is still the actual modular Hilbert pairing; its separate local
ordinary representative is not assumed by this theorem. -/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

/-- The genuine Laplacian representation gives the ordinary local gradient
integral against every compact upper-half-plane test, including seam-crossing tests. -/
theorem laplacian_periodizedUpperTest_weak_integral
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (hχone : ∀ z ∈ tsupport ψ, χ z = 1)
    (u : laplacian.domain) :
    (∫ z : ℂ,
      star (fderiv ℝ ψ z 1) * upperCutoffGradientOperator χ hχ hcχ hsχ 1
        (formLift ⟨u, laplacian_domain_le u.property⟩) z +
      star (fderiv ℝ ψ z Complex.I) * upperCutoffGradientOperator χ hχ hcχ hsχ Complex.I
        (formLift ⟨u, laplacian_domain_le u.property⟩) z) =
      inner ℂ (value (periodizedUpperCore ψ hψ hcψ hsψ)) (laplacian u) := by
  rw [← periodizedUpperCore_formGradient_integral χ hχ hcχ hsχ ψ hψ hcψ hsψ hχone]
  let P := periodizedUpperCore ψ hψ hcψ hsψ
  have hr := laplacian_representation u
    ⟨value P, gradient_le_closedGradient.1 (LinearMap.mem_range_self value P)⟩
  rw [closedGradient_apply_value] at hr
  have h := congrArg (starRingEnd ℂ) hr
  simpa only [inner_conj_symm, formGradient, formLift, Dirichlet.gradientValue_lift] using h.symm

/-- Ordinary convergence is retained together with the actual operator-source test pairing. -/
theorem laplacian_periodizedUpperTest_weak_pairing
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (hχone : ∀ z ∈ tsupport ψ, χ z = 1)
    (u : laplacian.domain) :
    Integrable (fun z : ℂ =>
      star (fderiv ℝ ψ z 1) * upperCutoffGradientOperator χ hχ hcχ hsχ 1
        (formLift ⟨u, laplacian_domain_le u.property⟩) z +
      star (fderiv ℝ ψ z Complex.I) * upperCutoffGradientOperator χ hχ hcχ hsχ Complex.I
        (formLift ⟨u, laplacian_domain_le u.property⟩) z) volume ∧
    (∫ z : ℂ,
      star (fderiv ℝ ψ z 1) * upperCutoffGradientOperator χ hχ hcχ hsχ 1
        (formLift ⟨u, laplacian_domain_le u.property⟩) z +
      star (fderiv ℝ ψ z Complex.I) * upperCutoffGradientOperator χ hχ hcχ hsχ Complex.I
        (formLift ⟨u, laplacian_domain_le u.property⟩) z) =
      inner ℂ (value (periodizedUpperCore ψ hψ hcψ hsψ)) (laplacian u) :=
  ⟨periodizedUpperCore_formGradient_integrable χ hχ hcχ hsχ ψ hψ hcψ _,
    laplacian_periodizedUpperTest_weak_integral χ hχ hcχ hsχ ψ hψ hcψ hsψ hχone u⟩

end GapFamily.Analytic
