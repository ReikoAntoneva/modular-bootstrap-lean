import GapFamily.Analytic.Spatial.SpatialOrbitRowIntegrable

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory

/-- A continuous spatial test multiplier and the actual joint orbit kernel preserve product
almost-everywhere strong measurability of every modular Hilbert input. -/
theorem aestronglyMeasurable_spatialOrbit_test_product (s : ℝ) (hs : 1 < s)
    (F : ModularHilbert) (a : UpperHalfPlane → ℂ) (ha : Continuous a) :
    AEStronglyMeasurable
      (fun p : UpperHalfPlane × UpperHalfPlane =>
        a p.1 * (spatialOrbitKernel (s : ℂ) p.1 p.2 * F p.2))
      ((volume : Measure UpperHalfPlane).prod modularMeasure) := by
  exact (ha.comp continuous_fst).aestronglyMeasurable.mul
    ((continuous_spatialOrbitKernel (s : ℂ) (by simpa using hs)).aestronglyMeasurable.mul
      (Lp.memLp F).aestronglyMeasurable.comp_snd)

end GapFamily.Analytic.SpatialPoint
