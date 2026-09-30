import GapFamily.Analytic.Spatial.SpatialOrbitBoundedUnfold
import GapFamily.Analytic.Spatial.SpatialModularBoundedEmbedding

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane Filter
open scoped MatrixGroups BoundedContinuousFunction

/-- The actual modular orbit integral operator with its exact full-mass normalization. -/
def normalizedOrbitOperator (s : ℝ) (hs : 1 < s) : ModularHilbert →L[ℂ] ModularHilbert :=
  ((((s - 1) / Real.pi : ℝ) : ℂ)) • spatialOrbitIntegralOperator s hs

/-- The actual embedded bounded test has an ordinarily integrable kernel product in every row. -/
theorem integrable_spatialOrbitKernel_mul_modularBoundedEmbedding (s : ℝ) (hs : 1 < s)
    (z : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ) :
    Integrable (fun w : UpperHalfPlane =>
      spatialOrbitKernel (s : ℂ) z w * modularBoundedEmbedding f w) modularMeasure := by
  apply (integrable_spatialOrbitKernel_mul_bounded s hs z f).congr
  filter_upwards [modularBoundedEmbedding_ae f] with w hw
  rw [hw]

/-- The actual modular L2 operator on an invariant bounded continuous test is the
ordinary whole-hyperbolic-plane kernel integral, almost everywhere for modularMeasure. -/
theorem spatialOrbitIntegralOperator_bounded_ae (s : ℝ) (hs : 1 < s)
    (f : UpperHalfPlane →ᵇ ℂ)
    (hmod : ∀ γ : SL(2, ℤ), ∀ w : UpperHalfPlane, f (γ • w) = f w) :
    spatialOrbitIntegralOperator s hs (modularBoundedEmbedding f) =ᵐ[modularMeasure]
      (fun z : UpperHalfPlane => ∫ w : UpperHalfPlane, pointKernel (s : ℂ) z w * f w ∂volume) := by
  filter_upwards [spatialOrbitIntegralOperator_ae s hs (modularBoundedEmbedding f)] with z hz
  rw [hz]
  calc
    _ = ∫ w : UpperHalfPlane, spatialOrbitKernel (s : ℂ) z w * f w ∂modularMeasure := by
      apply integral_congr_ae
      filter_upwards [modularBoundedEmbedding_ae f] with w hw
      rw [hw]
    _ = _ := integral_spatialOrbitKernel_mul_eq_whole s hs z f hmod

/-- The actual normalized modular operator equals the literal whole-H point average
on each invariant bounded continuous test, with all kernel products ordinarily integrable. -/
theorem normalizedOrbitOperator_bounded_ae (s : ℝ) (hs : 1 < s)
    (f : UpperHalfPlane →ᵇ ℂ)
    (hmod : ∀ γ : SL(2, ℤ), ∀ w : UpperHalfPlane, f (γ • w) = f w) :
    normalizedOrbitOperator s hs (modularBoundedEmbedding f) =ᵐ[modularMeasure]
      (fun z : UpperHalfPlane => pointAverage s z f) := by
  let c : ℂ := (((s - 1) / Real.pi : ℝ) : ℂ)
  have hsm := Lp.coeFn_smul c (spatialOrbitIntegralOperator s hs (modularBoundedEmbedding f))
  filter_upwards [spatialOrbitIntegralOperator_bounded_ae s hs f hmod, hsm] with z hz hcz
  change (c • spatialOrbitIntegralOperator s hs (modularBoundedEmbedding f)) z = _
  rw [hcz, Pi.smul_apply, hz]
  rfl

end GapFamily.Analytic.SpatialPoint
