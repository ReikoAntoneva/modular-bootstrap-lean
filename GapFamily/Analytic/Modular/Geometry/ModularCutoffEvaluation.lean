import GapFamily.Analytic.Modular.Geometry.ModularCutoffCoordinate
import GapFamily.Analytic.Modular.Elliptic.ModularRectangleEvaluation

/-!
# Actual local evaluation is unchanged by a cutoff equal to one

The true cutoff-domain vector has its existing continuous interior
representative multiplied by the literal smooth cutoff. Local restrictions
and evaluations therefore agree wherever that coefficient is one.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient.InteriorCutoff
open Set Filter MeasureTheory Dirichlet
open scoped Topology ContDiff

/-- Actual continuous representatives respect the proved operator-domain cutoff. -/
theorem operatorCutoff_representative (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (u : laplacian.domain) :
    EqOn (laplacianInteriorRepresentative
        (gradientLift laplacian (operatorCutoff χ hχ hc hs u)))
      (fun z => (χ z : ℂ) * laplacianInteriorRepresentative (gradientLift laplacian u) z)
      modularInterior := by
  apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_modularInterior
    (laplacianInteriorRepresentative_continuousOn _)
    ((Complex.continuous_ofReal.comp hχ.continuous).continuousOn.mul
      (laplacianInteriorRepresentative_continuousOn _))
  filter_upwards [laplacianInteriorRepresentative_ae
      (gradientLift laplacian (operatorCutoff χ hχ hc hs u)),
    operatorCutoff_coordinate_ae χ hχ hc hs u,
    laplacianInteriorRepresentative_ae (gradientLift laplacian u)] with z hv hm hu
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [hv, hm, hu]

/-- Equality on the observation set suffices for the genuine C(K) restriction. -/
theorem laplacianLocalRestriction_operatorCutoff
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ modularInterior)
    (hreg : K ⊆ closure (interior K))
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (hχK : EqOn χ (fun _ => 1) K) (u : laplacian.domain) :
    laplacianLocalRestriction K hKU hreg
      (gradientLift laplacian (operatorCutoff χ hχ hc hs u)) =
      laplacianLocalRestriction K hKU hreg (gradientLift laplacian u) := by
  apply ContinuousMap.ext
  intro z
  change laplacianInteriorRepresentative
      (gradientLift laplacian (operatorCutoff χ hχ hc hs u)) z =
    laplacianInteriorRepresentative (gradientLift laplacian u) z
  simpa only [hχK z.property, Complex.ofReal_one, one_mul] using
    operatorCutoff_representative χ hχ hc hs u (hKU z.property)

/-- The literal continuous rectangle restriction is preserved by the actual cutoff. -/
theorem laplacianRectangleRestriction_operatorCutoff
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hK : localEvaluationRectangle a b c d ⊆ modularInterior)
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (hχK : EqOn χ (fun _ => 1) (localEvaluationRectangle a b c d))
    (u : laplacian.domain) :
    laplacianRectangleRestriction a b c d hab hcd hK
      (gradientLift laplacian (operatorCutoff χ hχ hc hs u)) =
      laplacianRectangleRestriction a b c d hab hcd hK (gradientLift laplacian u) :=
  laplacianLocalRestriction_operatorCutoff _ hK (localEvaluationRectangle_regular hab hcd)
    χ hχ hc hs hχK u

/-- The actual bounded point evaluation agrees, including rectangle-boundary points. -/
theorem laplacianRectangleEvaluation_operatorCutoff
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hK : localEvaluationRectangle a b c d ⊆ modularInterior)
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (hχK : EqOn χ (fun _ => 1) (localEvaluationRectangle a b c d))
    (u : laplacian.domain) (z : localEvaluationRectangle a b c d) :
    laplacianRectangleEvaluation a b c d hab hcd hK z
      (gradientLift laplacian (operatorCutoff χ hχ hc hs u)) =
      laplacianRectangleEvaluation a b c d hab hcd hK z (gradientLift laplacian u) := by
  change laplacianRectangleRestriction a b c d hab hcd hK
      (gradientLift laplacian (operatorCutoff χ hχ hc hs u)) z =
    laplacianRectangleRestriction a b c d hab hcd hK (gradientLift laplacian u) z
  rw [laplacianRectangleRestriction_operatorCutoff a b c d hab hcd hK χ hχ hc hs hχK u]

/-- In particular, a cutoff equal to one on an open neighborhood of the rectangle
preserves the whole actual rectangle restriction. -/
theorem laplacianRectangleRestriction_operatorCutoff_of_neighborhood
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hK : localEvaluationRectangle a b c d ⊆ modularInterior)
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    {V : Set ℂ} (_hV : IsOpen V) (hKV : localEvaluationRectangle a b c d ⊆ V)
    (hχV : EqOn χ (fun _ => 1) V) (u : laplacian.domain) :
    laplacianRectangleRestriction a b c d hab hcd hK
      (gradientLift laplacian (operatorCutoff χ hχ hc hs u)) =
      laplacianRectangleRestriction a b c d hab hcd hK (gradientLift laplacian u) :=
  laplacianRectangleRestriction_operatorCutoff a b c d hab hcd hK χ hχ hc hs
    (hχV.mono hKV) u

end GapFamily.Analytic.ModularGradient.InteriorCutoff
