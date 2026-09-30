import Mathlib.MeasureTheory.VectorMeasure.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Reassembly of an actual signed measure across an atom-free cutoff. -/

open Set MeasureTheory

namespace GapFamily.Construction

/-- A signed measure with no atom at the cutoff is the sum of its two open
half-line restrictions. No support or density assumption is needed. -/
theorem signedMeasure_cutoff_partition (μ : SignedMeasure ℝ) (B : ℝ)
    (hB : μ {B} = 0) : μ = μ.restrict (Iio B) + μ.restrict (Ioi B) := by
  have hzero : μ.restrict {B} = 0 := by simp [hB]
  have hpartition := VectorMeasure.restrict_add_restrict_compl
    (v := μ) (measurableSet_singleton B)
  rw [hzero, zero_add, ← Iio_union_Ioi] at hpartition
  have hdisjoint : Disjoint (Iio B) (Ioi B) :=
    disjoint_left.mpr (fun x hx hy => lt_asymm (show x < B from hx) (show B < x from hy))
  rw [VectorMeasure.restrict_union hdisjoint measurableSet_Iio measurableSet_Ioi] at hpartition
  exact hpartition.symm

/-- Identifications below and above an atom-free cutoff assemble into an exact
global signed-measure identity. -/
theorem signedMeasure_eq_add_of_cutoff_restrict (μ μbelow μabove : SignedMeasure ℝ)
    (B : ℝ) (hB : μ {B} = 0)
    (hbelow : μ.restrict (Iio B) = μbelow) (habove : μ.restrict (Ioi B) = μabove) :
    μ = μbelow + μabove := by
  rw [signedMeasure_cutoff_partition μ B hB, hbelow, habove]

/-- Two atom-free signed measures agree globally when they agree on both sides
of the same cutoff. -/
theorem signedMeasure_eq_of_cutoff_restrict (μ ν : SignedMeasure ℝ) (B : ℝ)
    (hμ : μ {B} = 0) (hν : ν {B} = 0)
    (hbelow : μ.restrict (Iio B) = ν.restrict (Iio B))
    (habove : μ.restrict (Ioi B) = ν.restrict (Ioi B)) : μ = ν := by
  rw [signedMeasure_cutoff_partition μ B hμ, hbelow, habove]
  exact (signedMeasure_cutoff_partition ν B hν).symm

end GapFamily.Construction
