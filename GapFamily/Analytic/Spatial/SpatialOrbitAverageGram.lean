import GapFamily.Analytic.Foundation.L2NormalizedIndicator
import GapFamily.Analytic.Foundation.PositiveOperatorGram
import GapFamily.Analytic.Spatial.SpatialOrbitMeanZeroContinuation

/-! Positive finite matrices of genuine normalized spatial L² tests. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane
open scoped ComplexOrder

/-- The actual positive branch tested on normalized indicators, including
zero-mass sets through the ordinary inverse-zero convention. -/
def spatialOrbitAverageGram (s : ℝ) (hs : 1 / 2 < s) {ι : Type*}
    (S : ι → Set UpperHalfPlane) (hS : ∀ i, MeasurableSet (S i)) : Matrix ι ι ℂ :=
  fun i j => inner ℂ (L2NormalizedIndicator.vector modularMeasure (S i) (hS i))
    (spatialOrbitMeanZeroContinuation s hs
      (L2NormalizedIndicator.vector modularMeasure (S j) (hS j)))

theorem spatialOrbitAverageGram_posSemidef (s : ℝ) (hs : 1 / 2 < s)
    {ι : Type*} [Fintype ι] (S : ι → Set UpperHalfPlane)
    (hS : ∀ i, MeasurableSet (S i)) :
    (spatialOrbitAverageGram s hs S hS).PosSemidef :=
  PositiveOperatorGram.operatorGram_posSemidef _
    (spatialOrbitMeanZeroContinuation_isPositive s hs) _

/-- Each entry is the ordinary normalized target average of the actual
operator output; no pointwise representative equality is assumed. -/
theorem spatialOrbitAverageGram_entry (s : ℝ) (hs : 1 / 2 < s)
    {ι : Type*} (S : ι → Set UpperHalfPlane) (hS : ∀ i, MeasurableSet (S i)) (i j : ι) :
    spatialOrbitAverageGram s hs S hS i j =
      ⨍ z in S i, spatialOrbitMeanZeroContinuation s hs
        (L2NormalizedIndicator.vector modularMeasure (S j) (hS j)) z ∂modularMeasure :=
  L2NormalizedIndicator.inner_vector modularMeasure (S i) (hS i) _

end GapFamily.Analytic.SpatialPoint
