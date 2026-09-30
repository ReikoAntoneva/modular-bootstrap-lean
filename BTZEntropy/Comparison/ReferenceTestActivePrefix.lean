import BTZEntropy.Comparison.ReferenceTestDifference

/-! The finite set of actual active tail cells in a completed chronological
prefix. Invalid slots are removed only after proving their contribution zero. -/

noncomputable section

open Set MeasureTheory Real
open GapFamily GapFamily.Analytic GapFamily.Construction
open BTZEntropy.Construction
open scoped BigOperators Classical

namespace BTZEntropy.Comparison

/-- Every literal slot in the first `k` completed layers. -/
def slotPrefix (T k : ℕ) : Finset (LayerSlotIndex T) :=
  (Finset.range k).sigma (fun m => (Finset.univ : Finset (Fin (layerSlots (T + m)).length)))

@[simp] theorem mem_slotPrefix {T k : ℕ} (p : LayerSlotIndex T) :
    p ∈ slotPrefix T k ↔ p.1 < k := by
  simp [slotPrefix]

theorem sum_slotPrefix {T : ℕ} (k : ℕ) (f : LayerSlotIndex T → ℝ) :
    (∑ p ∈ slotPrefix T k, f p) =
      ∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length, f ⟨m, q⟩ :=
  Finset.sum_sigma _ _ _

variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
  (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)

/-- The finite prefix of actual valid cells, retaining the exact state
before every scheduled slot as part of validity. -/
def actualActivePrefix (k : ℕ) : Finset (d.ActiveSlot initial) :=
  (slotPrefix T k).subtype
    (fun p => RealTailStepValid a T (d.slotPreState initial p) p.layer p.row)

@[simp] theorem mem_actualActivePrefix (k : ℕ) (p : d.ActiveSlot initial) :
    p ∈ actualActivePrefix d initial k ↔ p.val.1 < k := by
  simp [actualActivePrefix]

@[simp] theorem actualActivePrefix_zero : actualActivePrefix d initial 0 = ∅ := by
  ext p
  simp

theorem actualActivePrefix_monotone : Monotone (actualActivePrefix d initial) := by
  intro k l hkl p hp
  exact (mem_actualActivePrefix d initial l p).mpr
    (((mem_actualActivePrefix d initial k p).mp hp).trans_le hkl)

/-- Every actual active slot occurs in a finite completed prefix. -/
theorem actualActivePrefix_complete (p : d.ActiveSlot initial) :
    p ∈ actualActivePrefix d initial (p.val.1 + 1) := by simp

/-- Any finite collection of actual cells is contained in one common
chronological prefix. -/
theorem finite_subset_actualActivePrefix (I : Finset (d.ActiveSlot initial)) :
    ∃ k, I ⊆ actualActivePrefix d initial k := by
  refine ⟨I.sup (fun p => p.val.1) + 1, ?_⟩
  intro p hp
  apply (mem_actualActivePrefix d initial _ p).mpr
  exact Nat.lt_succ_of_le
    (Finset.le_sup (f := fun p : d.ActiveSlot initial => p.val.1) hp)

/-- Filtering the exact scheduled prefix loses no contribution when every
invalid slot has been proved to contribute zero. -/
theorem sum_slots_eq_actualActivePrefix (k : ℕ) (f : LayerSlotIndex T → ℝ)
    (hzero : ∀ p, ¬RealTailStepValid a T (d.slotPreState initial p) p.layer p.row →
      f p = 0) :
    (∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length, f ⟨m, q⟩) =
      ∑ p ∈ actualActivePrefix d initial k, f p.val := by
  rw [actualActivePrefix, Finset.sum_subtype_eq_sum_filter, ← sum_slotPrefix]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  exact hzero p (fun hvalid => hnot (Finset.mem_filter.mpr ⟨hp, hvalid⟩))

theorem sum_scheduledQuadratureDifference_eq_activePrefix (f : ℝ → ℝ) (k : ℕ) :
    (∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
      scheduledQuadratureDifference d initial f ⟨m, q⟩) =
      ∑ p ∈ actualActivePrefix d initial k,
        scheduledQuadratureDifference d initial f p.val :=
  sum_slots_eq_actualActivePrefix d initial k _
    (scheduledQuadratureDifference_invalid d initial f)

theorem sum_scheduledDensityDifference_eq_activePrefix (f : ℝ → ℝ) (k : ℕ) :
    (∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
      scheduledDensityDifference d initial f ⟨m, q⟩) =
      ∑ p ∈ actualActivePrefix d initial k,
        scheduledDensityDifference d initial f p.val :=
  sum_slots_eq_actualActivePrefix d initial k _
    (scheduledDensityDifference_invalid d initial f)

theorem sum_scheduledDifference_eq_activePrefix (f : ℝ → ℝ) (k : ℕ) :
    (∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
      (scheduledQuadratureDifference d initial f ⟨m, q⟩ +
        scheduledDensityDifference d initial f ⟨m, q⟩)) =
      ∑ p ∈ actualActivePrefix d initial k,
        (scheduledQuadratureDifference d initial f p.val +
          scheduledDensityDifference d initial f p.val) := by
  apply sum_slots_eq_actualActivePrefix d initial k
    (fun p => scheduledQuadratureDifference d initial f p +
      scheduledDensityDifference d initial f p)
  intro p hp
  rw [scheduledQuadratureDifference_invalid d initial f p hp,
    scheduledDensityDifference_invalid d initial f p hp, add_zero]

/-- The finite active-prefix quadrature error has exactly the node-minus-
continuum form used by the uniform cell moment estimate. -/
theorem sum_scheduledQuadratureDifference_eq_packet (f : ℝ → ℝ) (k : ℕ) :
    (∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
      scheduledQuadratureDifference d initial f ⟨m, q⟩) =
      (∑ p ∈ actualActivePrefix d initial k, scheduledCellTest d initial
        (fun q => f q.1) p.val) -
      ∑ p ∈ actualActivePrefix d initial k,
        ∫ u in Ioo ((d.slotPreState initial p.val).front p.val.row)
          (d.activeCell initial p).right,
          (d.slotPreState initial p.val).numerator p.val.row u * f u
            ∂referenceMeasure p.val.row := by
  rw [sum_scheduledQuadratureDifference_eq_activePrefix]
  simp_rw [scheduledQuadratureDifference, scheduledCurrentCellTest_active]
  rw [Finset.sum_sub_distrib]

/-- The exact smooth-count difference is a sum over the finite set of
actual active cells to which the uniform local estimates apply. -/
theorem fixedFamily_smoothCount_sub_integerLeading_activePrefix
    {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}
    (D : FixedFamilyDatum g a δ) (φ : SmoothKernel) (E R : ℝ) (N k : ℕ)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hNv : E + R + gapFamilyCharge a / 12 < (N : ℝ))
    (hNp : E + R + 1 / 12 < (N : ℝ))
    (hk : E + R + 1 / 12 < ((g.start + k : ℕ) : ℝ)) :
    smoothCount φ (gapFamilyCharge a) D.spectrum E -
      integerLeadingSmoothCount φ (shift (gapFamilyCharge a)) g.start E =
      vacuumFiniteLevelCount φ (gapFamilyCharge a) E (descendantLevelCutoff N) +
      primaryDescendantTest φ E (descendantLevelCutoff N) δ +
      (D.initialState.nodes.map
        (fun p => primaryDescendantTest φ E (descendantLevelCutoff N) p.1)).sum -
      frontBoundaryTest (shift (gapFamilyCharge a)) g.start D.initialState.front
        (primaryDescendantTest φ E (descendantLevelCutoff N)) +
      ∑ p ∈ actualActivePrefix D.tail D.initialState k,
        (scheduledQuadratureDifference D.tail D.initialState
            (primaryDescendantTest φ E (descendantLevelCutoff N)) p.val +
          scheduledDensityDifference D.tail D.initialState
            (primaryDescendantTest φ E (descendantLevelCutoff N)) p.val) := by
  rw [fixedFamily_smoothCount_sub_integerLeading D φ E R N k hR hNv hNp hk,
    sum_scheduledDifference_eq_activePrefix]

end BTZEntropy.Comparison
