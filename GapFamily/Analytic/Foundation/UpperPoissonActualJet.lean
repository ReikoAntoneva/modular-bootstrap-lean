import GapFamily.Analytic.Foundation.UpperPoissonSourceOperator
import GapFamily.Analytic.Elliptic.LocalPoissonJet

/-!
The actual modular operator-domain fields form an ordinary local Poisson jet
on each open plateau of a smooth compact upper-half-plane cutoff. The source
coordinate is the bounded globally L² lift of the actual Laplacian value.
-/

noncomputable section
namespace GapFamily.Analytic.UpperSource
open Set MeasureTheory UpperHalfPlane ModularGradient LocalPoisson
open scoped ContDiff

/-- The genuine four-field jet of an actual modular Laplacian-domain element. -/
def actualJet (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (u : laplacian.domain) : Jet :=
  (upperCutoffValueOperator χ hχ hc hs (formLift ⟨u, laplacian_domain_le u.property⟩),
   upperCutoffGradientOperator χ hχ hc hs 1 (formLift ⟨u, laplacian_domain_le u.property⟩),
   upperCutoffGradientOperator χ hχ hc hs Complex.I (formLift ⟨u, laplacian_domain_le u.property⟩),
   sourceOperator χ hχ hc hs (laplacian u))

/-- The three distributional constraints follow from the proved actual weak
first derivatives and Poisson equation; no regularity witness is an input. -/
theorem actualJet_mem (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain) : actualJet χ hχ hc hs u ∈ jetSubmodule U := by
  intro ψ hψ hcψ hψU
  change inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ)
      (upperCutoffGradientOperator χ hχ hc hs 1
        (formLift ⟨u, laplacian_domain_le u.property⟩)) =
        -inner ℂ (upperTestDerivativeL2 ψ hψ hcψ 1)
          (upperCutoffValueOperator χ hχ hc hs (formLift ⟨u, laplacian_domain_le u.property⟩)) ∧
    inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ)
      (upperCutoffGradientOperator χ hχ hc hs Complex.I
        (formLift ⟨u, laplacian_domain_le u.property⟩)) =
        -inner ℂ (upperTestDerivativeL2 ψ hψ hcψ Complex.I)
          (upperCutoffValueOperator χ hχ hc hs (formLift ⟨u, laplacian_domain_le u.property⟩)) ∧
    inner ℂ (upperTestDerivativeL2 ψ hψ hcψ 1)
        (upperCutoffGradientOperator χ hχ hc hs 1
          (formLift ⟨u, laplacian_domain_le u.property⟩)) +
      inner ℂ (upperTestDerivativeL2 ψ hψ hcψ Complex.I)
        (upperCutoffGradientOperator χ hχ hc hs Complex.I
          (formLift ⟨u, laplacian_domain_le u.property⟩)) =
        inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ)
          (sourceOperator χ hχ hc hs (laplacian u))
  refine ⟨?_, ?_, ?_⟩
  · rw [euclideanCompactTest_inner, inner_derivativeTest_eq_integral]
    exact upperCutoff_weakDerivative_local χ hχ hc hs 1
      (formLift ⟨u, laplacian_domain_le u.property⟩) ψ hψ hcψ U hU hχU hψU
  · rw [euclideanCompactTest_inner, inner_derivativeTest_eq_integral]
    exact upperCutoff_weakDerivative_local χ hχ hc hs Complex.I
      (formLift ⟨u, laplacian_domain_le u.property⟩) ψ hψ hcψ U hU hχU hψU
  · rw [inner_derivativeTest_eq_integral, inner_derivativeTest_eq_integral,
      euclideanCompactTest_inner]
    have hp := laplacian_sourceOperator_weakPoisson_local χ hχ hc hs U hU hχU u
      ψ hψ hcψ hψU
    rw [integral_add
      (derivative_test_integrable ψ hψ hcψ 1
        (upperCutoffGradientOperator χ hχ hc hs 1
          (formLift ⟨u, laplacian_domain_le u.property⟩)))
      (derivative_test_integrable ψ hψ hcψ Complex.I
        (upperCutoffGradientOperator χ hχ hc hs Complex.I
          (formLift ⟨u, laplacian_domain_le u.property⟩)))] at hp
    exact hp

end GapFamily.Analytic.UpperSource
