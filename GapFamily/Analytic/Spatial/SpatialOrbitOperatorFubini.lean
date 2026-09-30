import GapFamily.Analytic.Spatial.SpatialOrbitTestProduct
import GapFamily.Analytic.Spatial.SpatialOrbitIntegralDerivative

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane

/-- The literal output pairs integrably with every continuous compact upper test. -/
theorem integrable_spatialOrbitIntegralFunction_test (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) :
    Integrable (fun z : UpperHalfPlane => a z * spatialOrbitIntegralFunction s f z) volume := by
  have hi := (integrable_spatialOrbitKernel_test_product s hs f a ha hc).integral_prod_left
  simpa only [spatialOrbitIntegralFunction, ofComplex_apply, integral_const_mul] using hi

/-- The opposite iterated pairing is integrable against the actual modular source measure. -/
theorem integrable_spatialOrbitKernel_test_source (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) :
    Integrable (fun w : UpperHalfPlane =>
      (∫ z : UpperHalfPlane, a z * spatialOrbitKernel (s : ℂ) z w) * f w) modularMeasure := by
  have hi := (integrable_spatialOrbitKernel_test_product s hs f a ha hc).integral_prod_right
  simpa only [← mul_assoc, integral_mul_const] using hi

/-- Genuine Fubini for compact tests of the actual ordinary integral representative. -/
theorem integral_spatialOrbitIntegralFunction_test (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) :
    (∫ z : UpperHalfPlane, a z * spatialOrbitIntegralFunction s f z) =
      ∫ w : UpperHalfPlane,
        (∫ z : UpperHalfPlane, a z * spatialOrbitKernel (s : ℂ) z w) * f w ∂modularMeasure := by
  have hi := integrable_spatialOrbitKernel_test_product s hs f a ha hc
  calc
    _ = ∫ z : UpperHalfPlane, ∫ w : UpperHalfPlane,
        a z * (spatialOrbitKernel (s : ℂ) z w * f w) ∂modularMeasure := by
      simp only [spatialOrbitIntegralFunction, ofComplex_apply, integral_const_mul]
    _ = ∫ w : UpperHalfPlane, ∫ z : UpperHalfPlane,
        a z * (spatialOrbitKernel (s : ℂ) z w * f w) ∂volume ∂modularMeasure :=
      integral_integral_swap hi
    _ = _ := by simp only [← mul_assoc, integral_mul_const]

end GapFamily.Analytic.SpatialPoint
