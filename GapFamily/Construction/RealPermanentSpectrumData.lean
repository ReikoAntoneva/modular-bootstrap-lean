import GapFamily.Construction.RealPermanentSpectrumGeometry
import GapFamily.Construction.RealPermanentSpectrumPrefix
import GapFamily.Construction.ScheduledPermanentSpectrumRemainderData
import GapFamily.Construction.PermanentSpectrumFirstPrimary
import GapFamily.Construction.ThermalCellLayer

/-!
# Permanent spectrum from the real-parameter repair recursion

The marker, the actual initial state list, and every emitted tail list retain
their individual occurrences. The finite prefix is literally the node field
of the same evolving repair state; no independent choice of nodes is made.
-/

noncomputable section

namespace GapFamily.Construction.RealTailLocalData

variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
  (d : RealTailLocalData a U T degree)
  (b : ℝ) (hb : 0 ≤ b) (hbT : b ≤ (T : ℝ)) (initial : FiniteRepairState)
  (hinitial : ∀ p ∈ initial.nodes, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)

/-- The repeated actual lists supply the permanent spectrum's finite indices. -/
def permanentSpectrumData : PermanentSpectrumData b :=
  PermanentSpectrumData.ofLists hb initial.nodes
    (scheduledAbsoluteLayerBlock T FiniteRepairState.front d.step d.nodeList initial)
    hinitial (d.scheduledAbsoluteLayerBlock_spectrum_bounds initial b hbT)

@[simp] theorem permanentSpectrumData_initialCount :
    (d.permanentSpectrumData b hb hbT initial hinitial).initialCount =
      initial.nodes.length := rfl

@[simp] theorem permanentSpectrumData_layerCount (m : ℕ) :
    (d.permanentSpectrumData b hb hbT initial hinitial).layerCount m =
      (scheduledAbsoluteLayerBlock T FiniteRepairState.front
        d.step d.nodeList initial m).length := rfl

theorem state_nodes (k : ℕ) :
    (d.state initial k).nodes =
      scheduledNodePrefix T FiniteRepairState.front d.step d.nodeList
        initial initial.nodes k :=
  scheduledLayerState_nodes FiniteRepairState.front FiniteRepairState.nodes
    d.step d.nodeList d.step_nodes T initial k

/-- The marker followed by the current state is exactly the permanent prefix. -/
theorem permanentSpectrumData_permanentAtomList (k : ℕ) :
    (d.permanentSpectrumData b hb hbT initial hinitial).permanentAtomList (T + k) =
      (b, 0) :: (d.state initial k).nodes := by
  rw [permanentSpectrumData, PermanentSpectrumData.ofLists_permanentAtomList]
  change (b, 0) :: (initial.nodes ++ (List.range (T + k)).flatMap
    (fun m => if T ≤ m then
      scheduledLayerBlock T FiniteRepairState.front d.step d.nodeList initial (m - T)
      else [])) = _
  rw [flatMap_range_zero_padded, d.state_nodes initial]
  simp only [scheduledNodePrefix, atomBlockPrefix, appendAtomBlocks, List.flatMap_def]

/-- The layer's thermal total is the ordinary finite sum over its actual list. -/
theorem permanentSpectrumData_layerThermal (t : ℝ) (m : ℕ) :
    (d.permanentSpectrumData b hb hbT initial hinitial).layerThermal t m =
      nodeListThermal t (scheduledAbsoluteLayerBlock T FiniteRepairState.front
        d.step d.nodeList initial m) := by
  unfold permanentSpectrumData
  exact PermanentSpectrumData.ofLists_layerThermal _ _ _ _ _ t m

theorem permanentSpectrumData_initial_strict
    (hstrict : ∀ p ∈ initial.nodes, b < p.1)
    (i : Fin (d.permanentSpectrumData b hb hbT initial hinitial).initialCount) :
    b < (d.permanentSpectrumData b hb hbT initial hinitial).initialEnergy i :=
  hstrict _ (List.get_mem initial.nodes i)

theorem permanentSpectrumData_layer_strict (hstrict : b < (T : ℝ))
    (m : ℕ) (i : Fin ((d.permanentSpectrumData b hb hbT initial hinitial).layerCount m)) :
    b < (d.permanentSpectrumData b hb hbT initial hinitial).layerEnergy m i :=
  d.scheduledAbsoluteLayerBlock_strict initial b hstrict m _ (List.get_mem _ i)

/-- Strict initial bounds and separation of the first tail layer prove that
the marker is the unique scalar primary at the first level, with count one. -/
theorem permanentSpectrumData_hasUnitScalarGap
    (hinitialStrict : ∀ p ∈ initial.nodes, b < p.1) (hbTStrict : b < (T : ℝ)) (c : ℝ) :
    HasUnitScalarGap ((d.permanentSpectrumData b hb hbT initial hinitial).spectrum c)
      (shift c + b) := by
  apply PermanentSpectrumData.hasUnitScalarGap
  · exact d.permanentSpectrumData_initial_strict b hb hbT initial hinitial hinitialStrict
  · exact d.permanentSpectrumData_layer_strict b hb hbT initial hinitial hbTStrict

end GapFamily.Construction.RealTailLocalData
