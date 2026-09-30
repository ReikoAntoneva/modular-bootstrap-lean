import GapFamily.Construction.RealTailRecurrence
import GapFamily.Construction.LayerSlotChronology
import GapFamily.Construction.ThermalEnvelopeDisjointCell
import GapFamily.Construction.ThermalCellLayer

/-! The actual valid cells of the real-charge scheduled iteration form a
disjoint family on each row. Their nodes and signed residuals therefore have
summable thermal masses, for every initial finite state.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction
namespace RealTailLocalData

variable {charge U : ℝ} {T : ℕ} {degree : ℕ → ℕ}

/-- The state immediately before a literal real-charge slot. -/
def slotPreState (d : RealTailLocalData charge U T degree) (initial : FiniteRepairState)
    (a : LayerSlotIndex T) : FiniteRepairState :=
  layerSlotPreState T FiniteRepairState.front
    d.step initial a

/-- Exactly the slots whose actual current state admits a real-charge cell. -/
abbrev ActiveSlot (d : RealTailLocalData charge U T degree) (initial : FiniteRepairState) :=
  {a : LayerSlotIndex T // RealTailStepValid charge T
    (slotPreState d initial a) a.layer a.row}

/-- The same selected cell used by the literal state update and node list. -/
def activeCell (d : RealTailLocalData charge U T degree) (initial : FiniteRepairState)
    (a : ActiveSlot d initial) :
    TailCell a.val.row
      ((slotPreState d initial a.val).front a.val.row)
      (degree a.val.layer)
      ((slotPreState d initial a.val).numerator a.val.row) :=
  d.cell _ _ _ a.property

variable (d : RealTailLocalData charge U T degree) (initial : FiniteRepairState)

/-- Validity makes the scheduler execute this cell, so its recorded interval
is exactly the cell's open interval. -/
theorem activeCell_interval_eq
    (a : ActiveSlot d initial) :
    layerSlotInterval T FiniteRepairState.front
      d.step initial a.val =
      Ioo ((slotPreState d initial a.val).front a.val.row)
        (activeCell d initial a).right := by
  change Ioo _ ((executeSlot a.val.layer FiniteRepairState.front
    (d.step a.val.layer) a.val.row
      (slotPreState d initial a.val)).front a.val.row) = _
  rw [executeSlot_of_uncleared _ _ _ _ _ a.property.front_upper]
  exact congrArg (Ioo _) (d.step_front_same a.property)

/-- Chronological monotonicity separates all actual cells on the same row. -/
theorem activeCell_pairwise_disjoint :
    Pairwise (fun a b : ActiveSlot d initial =>
      a.val.row = b.val.row →
      Disjoint
        (Ioo ((slotPreState d initial a.val).front a.val.row)
          (activeCell d initial a).right)
        (Ioo ((slotPreState d initial b.val).front b.val.row)
          (activeCell d initial b).right)) := by
  intro a b hne hrow
  rw [← activeCell_interval_eq d initial a,
    ← activeCell_interval_eq d initial b]
  exact layerSlotInterval_pairwise_disjoint T FiniteRepairState.front
    d.step initial
    d.step_front_mono
    (fun h => hne (Subtype.ext h)) hrow

theorem activeCell_front_lower
    (a : ActiveSlot d initial) :
    (T : ℝ) ≤
      (slotPreState d initial a.val).front a.val.row := by
  exact (show (T : ℝ) ≤ (a.val.layer : ℝ) by
    exact_mod_cast a.property.layer).trans a.property.front_lower

/-- Literal unit-node mass is summable over all actual valid scheduled cells. -/
theorem summable_activeCell_nodeMass
    (ha : 100 ≤ charge) (hT : (1 : ℝ) ≤ T) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : ActiveSlot d initial =>
      ∫ E, exp (-t * E) ∂(activeCell d initial a).nodeMeasure) := by
  exact summable_disjointTailCell_nodeMass
    (ι := ActiveSlot d initial)
    (fun a => a.val.row)
    (fun a => (slotPreState d initial a.val).front a.val.row)
    (fun a => degree a.val.layer)
    (fun a => (slotPreState d initial a.val).numerator a.val.row)
    (activeCell d initial)
    charge (T : ℝ)
    ha hT
    (activeCell_front_lower d initial)
    (fun a => a.property.physical)
    (activeCell_pairwise_disjoint d initial)
    (fun a => a.property.envelope) ht

/-- Ordinary thermal total variations of all actual cell residuals are summable. -/
theorem summable_activeCell_residual
    (ha : 100 ≤ charge) (hT : (1 : ℝ) ≤ T) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : ActiveSlot d initial =>
      ∫ E, exp (-t * E)
        ∂(activeCell d initial a).residual.variation) := by
  exact summable_disjointTailCell_residual
    (ι := ActiveSlot d initial)
    (fun a => a.val.row)
    (fun a => (slotPreState d initial a.val).front a.val.row)
    (fun a => degree a.val.layer)
    (fun a => (slotPreState d initial a.val).numerator a.val.row)
    (activeCell d initial)
    charge (T : ℝ)
    ha hT
    (activeCell_front_lower d initial)
    (fun a => a.property.physical)
    (activeCell_pairwise_disjoint d initial)
    (fun a => a.property.envelope) ht

/-- All literal node occurrences form a thermally summable sigma family. -/
theorem summable_activeCell_nodes
    (ha : 100 ≤ charge) (hT : (1 : ℝ) ≤ T) {t : ℝ} (ht : 0 < t) :
    Summable (fun p : Σ a : ActiveSlot d initial,
        Fin (activeCell d initial a).count =>
      exp (-t * (activeCell d initial p.1).node p.2)) := by
  apply (summable_sigma_of_nonneg (fun _ => exp_nonneg _)).mpr
  constructor
  · intro a
    exact Summable.of_finite
  · simpa only [tsum_fintype] using
      (summable_activeCell_nodeMass d initial ha hT ht).congr
        (fun a => (activeCell d initial a).integral_nodeMeasure
          (fun E => exp (-t * E)))

/-- The raw list records precisely the thermal integral of the selected cell's
unit-node measure. -/
theorem activeCell_nodeListThermal
    (a : ActiveSlot d initial) (t : ℝ) :
    nodeListThermal t (d.nodeList a.val.layer a.val.row
      (slotPreState d initial a.val)) =
      ∫ E, exp (-t * E) ∂(activeCell d initial a).nodeMeasure := by
  unfold nodeListThermal activeCell
  rw [nodeList, dite_eq_left a.property, TailCell.integral_nodeMeasure,
    List.map_ofFn, List.sum_ofFn]
  rfl

/-- The guard and validity test agree on every actual slot emission. -/
theorem scheduledSlotNodeList_eq_raw
    (a : LayerSlotIndex T) :
    scheduledSlotNodeList T FiniteRepairState.front
      d.step d.nodeList
      initial a =
      d.nodeList a.layer a.row (slotPreState d initial a) := by
  change (if (a.layer : ℝ) + 1 ≤
      (slotPreState d initial a).front a.row then []
    else d.nodeList a.layer a.row (slotPreState d initial a)) = _
  split_ifs with hskip
  · symm
    exact dite_eq_right (fun hvalid => (not_lt_of_ge hskip) hvalid.front_upper)
  · rfl

/-- Active actual guarded slot lists inherit the node-measure summability. -/
theorem summable_activeSlot_nodeListThermal
    (ha : 100 ≤ charge) (hT : (1 : ℝ) ≤ T) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : ActiveSlot d initial =>
      nodeListThermal t (scheduledSlotNodeList T FiniteRepairState.front
        d.step d.nodeList
        initial a.val)) := by
  simpa only [scheduledSlotNodeList_eq_raw,
    activeCell_nodeListThermal] using
    summable_activeCell_nodeMass d initial ha hT ht

end RealTailLocalData
end GapFamily.Construction
