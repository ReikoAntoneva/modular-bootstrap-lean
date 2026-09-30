import GapFamily.Analytic.Spatial.SpatialPointKernelMass
import GapFamily.Analytic.Spatial.SpatialPointKernelMassInvariant

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane

/-- The prescribed point kernel is genuinely integrable over the whole
hyperbolic upper half-plane for every real exponent greater than one. -/
theorem integrable_pointKernel (s : ℝ) (hs : 1 < s) (w : UpperHalfPlane) :
    Integrable (fun z : UpperHalfPlane => pointKernel (s : ℂ) z w) volume := by
  exact (integrable_pointKernel_iff_I (s : ℂ) w).mpr (integrable_pointKernel_I s hs)

/-- The exact full hyperbolic mass retains the source's constant quarter normalization. -/
theorem integral_pointKernel (s : ℝ) (hs : 1 < s) (w : UpperHalfPlane) :
    (∫ z : UpperHalfPlane, pointKernel (s : ℂ) z w) =
      (Real.pi / (s - 1) : ℝ) := by
  rw [integral_pointKernel_eq_I]
  exact integral_pointKernel_I s hs

end GapFamily.Analytic.SpatialPoint
