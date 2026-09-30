import GapFamily.Analytic.Spatial.SpatialOrbitOperator
import GapFamily.Analytic.Spatial.SpatialPointKernelTest

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane
open scoped MatrixGroups BoundedContinuousFunction

/-- Bounded continuous tests have genuinely integrable orbit-kernel products in every row. -/
theorem integrable_spatialOrbitKernel_mul_bounded (s : ℝ) (hs : 1 < s)
    (z : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ) :
    Integrable (fun w : UpperHalfPlane => spatialOrbitKernel (s : ℂ) z w * f w) modularMeasure := by
  have hk : Integrable (fun w : UpperHalfPlane => spatialOrbitKernel (s : ℂ) z w) modularMeasure := by
    simpa only [spatialOrbitKernel_symm (s : ℂ) z] using
      integrable_spatialOrbitKernel (s : ℂ) (by simpa using hs) z
  exact hk.mul_bdd f.continuous.aestronglyMeasurable (Filter.Eventually.of_forall f.norm_coe_le_norm)

/-- Modularity of the actual test moves its value inside the literal half-weighted orbit sum. -/
theorem spatialOrbitKernel_mul_eq_half_tsum (s : ℂ) (z w : UpperHalfPlane)
    (f : UpperHalfPlane →ᵇ ℂ)
    (hmod : ∀ γ : SL(2, ℤ), ∀ w : UpperHalfPlane, f (γ • w) = f w) :
    spatialOrbitKernel s z w * f w =
      (1 / 2 : ℂ) * ∑' γ : SL(2, ℤ), pointKernel s z (γ • w : UpperHalfPlane) * f (γ • w) := by
  rw [spatialOrbitKernel_eq_half_tsum_right]
  simp_rw [hmod]
  rw [tsum_mul_right]
  ring

/-- The actual full matrix tiling factor two cancels exactly the orbit kernel's halfweight.
Every integral here is ordinary, with integrability supplied by the bounded test and kernel mass. -/
theorem integral_spatialOrbitKernel_mul_eq_whole (s : ℝ) (hs : 1 < s)
    (z : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ)
    (hmod : ∀ γ : SL(2, ℤ), ∀ w : UpperHalfPlane, f (γ • w) = f w) :
    (∫ w : UpperHalfPlane, spatialOrbitKernel (s : ℂ) z w * f w ∂modularMeasure) =
      ∫ w : UpperHalfPlane, pointKernel (s : ℂ) z w * f w ∂volume := by
  simp_rw [spatialOrbitKernel_mul_eq_half_tsum (s : ℂ) z _ f hmod]
  rw [integral_const_mul,
    integral_modularAction_tsum_eq_two_mul (integrable_pointKernel_mul_bounded s hs z f)]
  ring

end GapFamily.Analytic.SpatialPoint
