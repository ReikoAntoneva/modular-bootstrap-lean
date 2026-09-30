import GapFamily.Construction.RealTailCellThermal

/-! Thermal convergence of the literal real-charge tail schedule. Actual
cell disjointness gives convergence of all emitted lists, without an input
thermal summability assertion about the infinite spectrum. -/

noncomputable section

open Set MeasureTheory Real

namespace GapFamily.Construction
namespace RealTailLocalData

variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
variable (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)

theorem scheduledSlotNodeList_inactive
    (p : LayerSlotIndex T)
    (hp : ¬RealTailStepValid a T (d.slotPreState initial p) p.layer p.row) :
    scheduledSlotNodeList T FiniteRepairState.front d.step d.nodeList initial p = [] := by
  rw [d.scheduledSlotNodeList_eq_raw]
  exact dite_eq_right hp

/-- Every slot uses its actual pre-state and retains each emitted occurrence. -/
theorem scheduledSlotNodeList_thermal_active
    (p : d.ActiveSlot initial) (t : ℝ) :
    nodeListThermal t (scheduledSlotNodeList T FiniteRepairState.front
      d.step d.nodeList initial p) =
      ∫ E, exp (-t * E) ∂(d.activeCell initial p).nodeMeasure := by
  rw [d.scheduledSlotNodeList_eq_raw, d.activeCell_nodeListThermal]

/-- The full slot family has a convergent thermal sum. -/
theorem summable_slotNode_thermal
    (ha : 100 ≤ a) (hT : (1 : ℝ) ≤ T) {t : ℝ} (ht : 0 < t) :
    Summable (fun p : LayerSlotIndex T =>
      nodeListThermal t (scheduledSlotNodeList T FiniteRepairState.front
        d.step d.nodeList initial p)) := by
  apply summable_nodeListThermal_of_active
    (fun p : LayerSlotIndex T => RealTailStepValid a T
      (d.slotPreState initial p) p.layer p.row)
    _ t (d.scheduledSlotNodeList_inactive initial)
  exact d.summable_activeSlot_nodeListThermal initial ha hT ht

/-- The actual emitted layer lists have a finite total thermal sum. -/
theorem summable_layerBlock_thermal
    (ha : 100 ≤ a) (hT : (1 : ℝ) ≤ T) {t : ℝ} (ht : 0 < t) :
    Summable (fun m => nodeListThermal t
      (scheduledLayerBlock T FiniteRepairState.front d.step d.nodeList initial m)) :=
  summable_scheduledLayerBlock_thermal _ _ _ _ _ t
    (d.summable_slotNode_thermal initial ha hT ht)

/-- Padding before the first layer preserves convergence in absolute indexing. -/
theorem summable_absoluteLayerBlock_thermal
    (ha : 100 ≤ a) (hT : (1 : ℝ) ≤ T) {t : ℝ} (ht : 0 < t) :
    Summable (fun m => nodeListThermal t
      (scheduledAbsoluteLayerBlock T FiniteRepairState.front d.step d.nodeList initial m)) :=
  summable_scheduledAbsoluteLayerBlock_thermal _ _ _ _ _ t
    (d.summable_slotNode_thermal initial ha hT ht)

end RealTailLocalData
end GapFamily.Construction
