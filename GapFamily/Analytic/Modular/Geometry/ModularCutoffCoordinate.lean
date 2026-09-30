import GapFamily.Analytic.Modular.Geometry.ModularCutoffLaplacian
import GapFamily.Analytic.Modular.Elliptic.ModularLocalEvaluation

/-!
# Actual operator cutoff in modular coordinates

The proved form multiplier preserves the Laplacian domain. Its graph-coordinate
value is multiplication by the literal smooth cutoff, almost everywhere for
ordinary Lebesgue measure on the modular interior.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient.InteriorCutoff

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- The actual cutoff of a Laplacian-domain vector, with domain membership
supplied by the proved multiplier identity. -/
def operatorCutoff (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (u : laplacian.domain) : laplacian.domain :=
  ⟨formEmbedding (formMultiplier χ hχ hc hs (operatorForm u)),
    formMultiplier_mem_laplacian_domain χ hχ hc hs u⟩

/-- The cutoff's actual Hilbert value is the existing bounded multiplier. -/
theorem operatorCutoff_value (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (u : laplacian.domain) :
    (operatorCutoff χ hχ hc hs u : ModularHilbert) = valueMultiplier χ hχ hc u := by
  change formEmbedding (formMultiplier χ hχ hc hs (operatorForm u)) = _
  rw [formMultiplier_value, operatorForm_value]

/-- The actual graph-coordinate representative of the operator cutoff is the
literal product, with the transported measure replaced by its equivalent
ordinary interior Lebesgue null sets. -/
theorem operatorCutoff_coordinate_ae (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (u : laplacian.domain) :
    laplacianGraphCoordinate (Dirichlet.gradientLift laplacian (operatorCutoff χ hχ hc hs u))
      =ᵐ[volume.restrict modularInterior]
        (fun z => (χ z : ℂ) * laplacianGraphCoordinate (Dirichlet.gradientLift laplacian u) z) := by
  have heq (v : laplacian.domain) :
      laplacianGraphCoordinate (Dirichlet.gradientLift laplacian v) =
        modularCoordinateEquiv.symm (v : ModularHilbert) := rfl
  rw [heq, heq]
  apply (ae_modularCoordinate_iff_restrict _).mp
  apply (ae_modularCoordinate_iff _).mpr
  have hleft := modularCoordinateEquiv_apply_ae
    (modularCoordinateEquiv.symm (operatorCutoff χ hχ hc hs u : ModularHilbert))
  have hright := modularCoordinateEquiv_apply_ae
    (modularCoordinateEquiv.symm (u : ModularHilbert))
  simp only [LinearIsometryEquiv.apply_symm_apply] at hleft hright
  have hm := realMultiplier_ae χ hχ.continuous hc (u : ModularHilbert)
  change valueMultiplier χ hχ hc u =ᵐ[modularMeasure]
    (fun τ : UpperHalfPlane => (χ τ : ℂ) * (u : ModularHilbert) τ) at hm
  filter_upwards [hleft, hright, hm] with τ hleft hright hm
  rw [← hleft, ← hright, operatorCutoff_value, hm]

end GapFamily.Analytic.ModularGradient.InteriorCutoff
