import GapFamily.Analytic.Modular.Elliptic.ModularUpperCompactEvaluation
import GapFamily.Analytic.Modular.Elliptic.ModularUpperValueCoherence

/-!
# Coherent compact upper-half-plane evaluation

The actual graph-domain observation operators agree on nested compact sets,
even when different auxiliary cutoff plateaus were used to construct them.
The equality is pointwise on the whole compact set, including thin subsets
and modular seams.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set UpperHalfPlane
open scoped ContDiff

/-- Actual compact evaluation is independent of the auxiliary cutoff and
commutes with restriction to a smaller compact observation set. -/
theorem laplacianUpperCompactRestriction_coherent
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (η : ℂ → ℂ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ upperHalfPlaneSet)
    (U V : Set ℂ) (hU : IsOpen U) (hV : IsOpen V)
    (hχU : EqOn χ (fun _ => 1) U) (hηV : EqOn η (fun _ => 1) V)
    (K₁ K₂ : Set ℂ) [CompactSpace K₁] [CompactSpace K₂]
    (h₁₂ : K₁ ⊆ K₂) (h₁U : K₁ ⊆ U) (h₂V : K₂ ⊆ V) :
    laplacianUpperCompactRestriction χ hχ hcχ hsχ U hU hχU K₁ h₁U =
      (ContinuousMap.compCLM ℂ ℂ (ContinuousMap.inclusion h₁₂)).comp
        (laplacianUpperCompactRestriction η hη hcη hsη V hV hηV K₂ h₂V) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousMap.ext
  intro z
  exact laplacianUpperRepresentative_eqOn_overlap χ hχ hcχ hsχ η hη hcη hsη
    U V hU hV hχU hηV u ⟨h₁U z.property, h₂V (h₁₂ z.property)⟩

end GapFamily.Analytic.ModularGradient
