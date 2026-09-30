import GapFamily.Analytic.Modular.ModularClosedSourcePairing
import GapFamily.Analytic.Modular.ModularLaplacianUpperTest
import GapFamily.Analytic.Modular.Elliptic.ModularUpperCutoffWeakGradientLocal
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticLocalL2

/-! Actual ordinary local weak Poisson equations across modular seams. -/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

/-- The actual local source divided by y² is genuinely L² on every compact upper chart. -/
theorem upperCutoffSourceField_memLp_on_compact
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet) (f : ModularHilbert)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ upperHalfPlaneSet) :
    MemLp (upperCutoffSourceField χ hχ hcχ hsχ f) 2 (volume.restrict K) := by
  have hinv : ContinuousOn (fun z : ℂ => ((z.im : ℂ) ^ 2)⁻¹) K := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro z hz
      exact pow_ne_zero 2 (by exact_mod_cast (hKU hz).ne')
  change MemLp (fun z : ℂ => upperCutoffHilbertValueOperator χ hχ hcχ hsχ f z /
    (z.im : ℂ) ^ 2) 2 (volume.restrict K)
  simpa only [div_eq_mul_inv] using
    memLp_mul_continuousOn_compact hK
      ((Lp.memLp (upperCutoffHilbertValueOperator χ hχ hcχ hsχ f)).restrict K) hinv

/-- The genuine operator-domain field satisfies an ordinary local Poisson test equation. -/
theorem laplacian_upper_weakPoisson_test
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
      ∫ z : ℂ, star (ψ z) * upperCutoffSourceField χ hχ hcχ hsχ (laplacian u) z := by
  rw [laplacian_periodizedUpperTest_weak_integral χ hχ hcχ hsχ ψ hψ hcψ hsψ hχone u,
    periodizedUpperCore_hilbert_source_integral χ hχ hcχ hsχ ψ hψ hcψ hsψ hχone]

/-- Both sides of the genuine local Poisson equation are ordinary convergent integrals. -/
theorem laplacian_upper_weakPoisson_integrable
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (u : laplacian.domain) :
    Integrable (fun z : ℂ =>
      star (fderiv ℝ ψ z 1) * upperCutoffGradientOperator χ hχ hcχ hsχ 1
        (formLift ⟨u, laplacian_domain_le u.property⟩) z +
      star (fderiv ℝ ψ z Complex.I) * upperCutoffGradientOperator χ hχ hcχ hsχ Complex.I
        (formLift ⟨u, laplacian_domain_le u.property⟩) z) volume ∧
    Integrable (fun z : ℂ => star (ψ z) *
      upperCutoffSourceField χ hχ hcχ hsχ (laplacian u) z) volume :=
  ⟨periodizedUpperCore_formGradient_integrable χ hχ hcχ hsχ ψ hψ hcψ _,
    upperCutoffSourceField_test_integrable χ hχ hcχ hsχ ψ hψ hcψ hsψ (laplacian u)⟩

/-- On an actual open plateau the constructed local value and gradient fields
satisfy the weak derivative identities and the actual ordinary Poisson equation.
There is no regularity premise on the operator-domain vector. -/
theorem laplacian_upper_weakPoisson_local
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    (∀ v : ℂ, (∫ z : ℂ, star (ψ z) * upperCutoffGradientOperator χ hχ hcχ hsχ v
        (formLift ⟨u, laplacian_domain_le u.property⟩) z) =
      -(∫ z : ℂ, star (fderiv ℝ ψ z v) * upperCutoffValueOperator χ hχ hcχ hsχ
        (formLift ⟨u, laplacian_domain_le u.property⟩) z)) ∧
    (∫ z : ℂ,
      star (fderiv ℝ ψ z 1) * upperCutoffGradientOperator χ hχ hcχ hsχ 1
        (formLift ⟨u, laplacian_domain_le u.property⟩) z +
      star (fderiv ℝ ψ z Complex.I) * upperCutoffGradientOperator χ hχ hcχ hsχ Complex.I
        (formLift ⟨u, laplacian_domain_le u.property⟩) z) =
      ∫ z : ℂ, star (ψ z) * upperCutoffSourceField χ hχ hcχ hsχ (laplacian u) z := by
  have hχone : ∀ z ∈ tsupport ψ, χ z = 1 := fun z hz => hχU (hψU hz)
  have hsψ : tsupport ψ ⊆ upperHalfPlaneSet := by
    intro z hz
    apply hsχ
    apply subset_tsupport χ
    rw [Function.mem_support, hχone z hz]
    exact one_ne_zero
  refine ⟨fun v => upperCutoff_weakDerivative_local χ hχ hcχ hsχ v
    (formLift ⟨u, laplacian_domain_le u.property⟩) ψ hψ hcψ U hU hχU hψU, ?_⟩
  exact laplacian_upper_weakPoisson_test χ hχ hcχ hsχ ψ hψ hcψ hsψ hχone u

end GapFamily.Analytic
