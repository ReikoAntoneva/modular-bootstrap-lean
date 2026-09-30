import BTZEntropy.Comparison.ReferenceTestActivePrefix
import BTZEntropy.Comparison.DiscreteReferenceDensity
import BTZEntropy.Comparison.DiscreteReferenceBoundary

/-! The exact actual-cell decomposition used by the uniform comparison. -/

noncomputable section

open Set MeasureTheory Real
open GapFamily GapFamily.Analytic GapFamily.Construction
open BTZEntropy.Construction
open scoped BigOperators Classical

namespace BTZEntropy.Comparison

theorem sum_scheduledDensityDifference_eq_actual
    {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}
    (d : BTZEntropy.Construction.FixedFamilyDatum g a δ) (φ : SmoothKernel)
    (E : ℝ) (F : Finset (ℕ × ℕ))
    (I : Finset (d.tail.ActiveSlot d.initialState)) :
    (∑ p ∈ I, scheduledDensityDifference d.tail d.initialState
      (primaryDescendantTest φ E F) p.val) =
      FixedFamilyDatum.activeCellDensityErrorPacket d φ E F I := by
  unfold FixedFamilyDatum.activeCellDensityErrorPacket
  apply Finset.sum_congr rfl
  intro p hp
  rw [scheduledDensityDifference, scheduledCurrentCellTest_active,
    scheduledLeadingCellTest_active]
  exact (FixedFamilyDatum.activeCell_densityError_integral_eq d φ E F p).symm

/-- This identity retains the literal prestate numerator in every actual
cell and the finite initial list, including repeated unit nodes. -/
theorem fixedFamily_smoothCount_sub_integerLeading_decomposed
    {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}
    (d : BTZEntropy.Construction.FixedFamilyDatum g a δ) (φ : SmoothKernel)
    (E R : ℝ) (N k : ℕ)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hNv : E + R + gapFamilyCharge a / 12 < (N : ℝ))
    (hNp : E + R + 1 / 12 < (N : ℝ))
    (hk : E + R + 1 / 12 < ((g.start + k : ℕ) : ℝ)) :
    smoothCount φ (gapFamilyCharge a) d.spectrum E -
      integerLeadingSmoothCount φ (shift (gapFamilyCharge a)) g.start E =
      vacuumFiniteLevelCount φ (gapFamilyCharge a) E (descendantLevelCutoff N) +
      primaryDescendantTest φ E (descendantLevelCutoff N) δ +
      (d.initialState.nodes.map
        (fun p => primaryDescendantTest φ E (descendantLevelCutoff N) p.1)).sum -
      fixedFamilyBoundaryPacket φ d E (descendantLevelCutoff N) +
      ((∑ p ∈ actualActivePrefix d.tail d.initialState k,
          scheduledCellTest d.tail d.initialState
            (fun q => primaryDescendantTest φ E (descendantLevelCutoff N) q.1) p.val) -
        ∑ p ∈ actualActivePrefix d.tail d.initialState k,
          ∫ u in Ioo ((d.tail.slotPreState d.initialState p.val).front p.val.row)
            (d.tail.activeCell d.initialState p).right,
            (d.tail.slotPreState d.initialState p.val).numerator p.val.row u *
              primaryDescendantTest φ E (descendantLevelCutoff N) u
                ∂referenceMeasure p.val.row) +
      FixedFamilyDatum.activeCellDensityErrorPacket d φ E (descendantLevelCutoff N)
        (actualActivePrefix d.tail d.initialState k) := by
  rw [fixedFamily_smoothCount_sub_integerLeading_activePrefix d φ E R N k
    hR hNv hNp hk, Finset.sum_add_distrib,
    sum_scheduledDensityDifference_eq_actual]
  simp only [scheduledQuadratureDifference, scheduledCurrentCellTest_active,
    Finset.sum_sub_distrib, fixedFamilyBoundaryPacket]
  ring

end BTZEntropy.Comparison
