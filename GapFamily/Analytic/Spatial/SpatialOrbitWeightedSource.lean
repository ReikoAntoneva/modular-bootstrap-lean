import GapFamily.Analytic.Spatial.SpatialOrbitSourceBound
import GapFamily.Analytic.Spatial.SpatialOrbitParameterAnalytic
import GapFamily.Analytic.Modular.Geometry.ModularHeightPowerLp
import GapFamily.Analytic.Cusp.Profile.CuspWeightedInput

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane

/-- The literal point-source kernel belongs to the actual weighted modular L²
space throughout its original convergence half-plane. -/
theorem memLp_spatialOrbitKernel_weighted (α : ℝ) (hα : 0 ≤ α)
    (hhalf : α < 1 / 2) (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    MemLp (fun z : UpperHalfPlane => ((z.im ^ α : ℝ) : ℂ) * spatialOrbitKernel s z w)
      2 modularMeasure := by
  obtain ⟨C, _, hb⟩ := exists_spatialOrbitKernel_bound s.re hs w
  apply memLp_modularHeightPower_mul_of_bound α hα hhalf
    (((continuous_spatialOrbitKernel s hs).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
  exact Eventually.of_forall fun z =>
    (spatialOrbitKernel_norm_le_real_exponent hs le_rfl z w).trans (hb z)

/-- Actual height-weighted point source in modular L²; zero outside the original
convergence region is solely a totalization, with no continuation asserted. -/
def spatialOrbitWeightedSource (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    (s : ℂ) (w : UpperHalfPlane) : ModularHilbert :=
  if hs : 1 < s.re then (memLp_spatialOrbitKernel_weighted α hα hhalf s hs w).toLp _ else 0

/-- The constructed completed-space element has its literal weighted representative. -/
theorem spatialOrbitWeightedSource_ae (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    spatialOrbitWeightedSource α hα hhalf s w =ᵐ[modularMeasure]
      (fun z : UpperHalfPlane => ((z.im ^ α : ℝ) : ℂ) * spatialOrbitKernel s z w) := by
  rw [spatialOrbitWeightedSource, dite_eq_left hs]
  exact (memLp_spatialOrbitKernel_weighted α hα hhalf s hs w).coeFn_toLp

/-- Removing the actual cusp weight recovers the unweighted literal point source. -/
theorem cuspWeightedInput_spatialOrbitWeightedSource_ae (α : ℝ) (hα : 0 ≤ α)
    (hhalf : α < 1 / 2) (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    cuspWeightedInput α hα (spatialOrbitWeightedSource α hα hhalf s w) =ᵐ[modularMeasure]
      (fun z : UpperHalfPlane => spatialOrbitKernel s z w) := by
  filter_upwards [cuspWeightedInput_ae α hα (spatialOrbitWeightedSource α hα hhalf s w),
    spatialOrbitWeightedSource_ae α hα hhalf s hs w] with z hz hzw
  rw [hz, hzw, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add z.im_pos,
    neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]

end GapFamily.Analytic.SpatialPoint
