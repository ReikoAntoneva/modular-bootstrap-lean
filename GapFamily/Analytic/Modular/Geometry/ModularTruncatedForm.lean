import GapFamily.Analytic.Modular.Geometry.ModularTruncatedIndicator
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore

/-!
# Actual bounded-height restriction of the modular form domain

This is literal multiplication by the low-height indicator in the actual
modular Hilbert space. Compactness is supplied separately by the concrete
cutoff and coordinate transport construction.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane

/-- The actual bounded-height restriction, zero-extended in the modular Hilbert space. -/
def truncatedFormEmbedding (H : ℝ) : FormDomain →L[ℂ] ModularHilbert :=
  (modularLowCut H).comp formEmbedding

theorem truncatedFormEmbedding_ae (H : ℝ) (u : FormDomain) :
    truncatedFormEmbedding H u =ᵐ[modularMeasure]
      {τ : UpperHalfPlane | τ.im ≤ H}.indicator (formEmbedding u) :=
  modularLowCut_ae H (formEmbedding u)

@[simp] theorem truncatedFormEmbedding_coreForm (H : ℝ) (F : smoothCore) :
    truncatedFormEmbedding H (coreForm F) = modularLowCut H (value F) := rfl

theorem norm_truncatedFormEmbedding_le (H : ℝ) (u : FormDomain) :
    ‖truncatedFormEmbedding H u‖ ≤ ‖u‖ :=
  (norm_modularLowCut_le H (formEmbedding u)).trans
    (Dirichlet.gradientEmbedding_norm_le closedGradient u)

theorem truncatedFormEmbedding_norm_le_one (H : ℝ) :
    ‖truncatedFormEmbedding H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using norm_truncatedFormEmbedding_le H u

end GapFamily.Analytic.ModularGradient
