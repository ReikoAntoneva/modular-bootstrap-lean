import GapFamily.Construction.RealTailRecurrence
import GapFamily.Construction.LayerScheduleNode

/-!
# Physical location of the real-parameter tail nodes

The validity guard enforces each actual cell's layer and cone bounds. Every
other branch emits the empty list, so the bounds hold without a reachability
hypothesis on the input finite state.
-/

noncomputable section

namespace GapFamily.Construction.RealTailLocalData

variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
  (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)

theorem scheduledLayerBlock_bounds (k : ℕ) (p : ℝ × ℤ)
    (hp : p ∈ scheduledLayerBlock T FiniteRepairState.front d.step d.nodeList initial k) :
    ((T + k : ℕ) : ℝ) ≤ p.1 ∧ p.1 < ((T + k : ℕ) : ℝ) + 2 ∧
      |(p.2 : ℝ)| ≤ p.1 := by
  unfold scheduledLayerBlock at hp
  refine layerNodeBlock_property (P := fun _ : FiniteRepairState => True)
    (Q := fun q => ((T + k : ℕ) : ℝ) ≤ q.1 ∧
      q.1 < ((T + k : ℕ) : ℝ) + 2 ∧ |(q.2 : ℝ)| ≤ q.1) trivial
    (fun _ _ _ _ => trivial) ?_ p hp
  intro J _ state _ q hq
  have hraw := ((mem_guardedSlotNodes_iff (T + k) FiniteRepairState.front
    (d.nodeList (T + k)) J state q).mp hq).2
  exact d.nodeList_layer_bounds (T + k) J state q hraw

theorem scheduledAbsoluteLayerBlock_bounds (m : ℕ) (p : ℝ × ℤ)
    (hp : p ∈ scheduledAbsoluteLayerBlock T FiniteRepairState.front
      d.step d.nodeList initial m) :
    (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2 ∧ |(p.2 : ℝ)| ≤ p.1 := by
  unfold scheduledAbsoluteLayerBlock at hp
  split_ifs at hp with hm
  · simpa only [Nat.add_sub_of_le hm] using
      d.scheduledLayerBlock_bounds initial (m - T) p hp
  · simp only [List.not_mem_nil] at hp

theorem scheduledAbsoluteLayerBlock_spectrum_bounds (b : ℝ) (hbT : b ≤ (T : ℝ))
    (m : ℕ) (p : ℝ × ℤ)
    (hp : p ∈ scheduledAbsoluteLayerBlock T FiniteRepairState.front
      d.step d.nodeList initial m) :
    b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1 ∧ (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2 := by
  have hm : (T : ℝ) ≤ (m : ℝ) :=
    Nat.cast_le.mpr (scheduledAbsoluteLayerBlock_mem_start hp)
  obtain ⟨hlo, hhi, hphysical⟩ := d.scheduledAbsoluteLayerBlock_bounds initial m p hp
  exact ⟨hbT.trans (hm.trans hlo), hphysical, hlo, hhi⟩

/-- A strict separation between the marker and the first tail layer is enough
to exclude every tail occurrence from the marker level. -/
theorem scheduledAbsoluteLayerBlock_strict (b : ℝ) (hbT : b < (T : ℝ))
    (m : ℕ) (p : ℝ × ℤ)
    (hp : p ∈ scheduledAbsoluteLayerBlock T FiniteRepairState.front
      d.step d.nodeList initial m) : b < p.1 := by
  have hm : (T : ℝ) ≤ (m : ℝ) :=
    Nat.cast_le.mpr (scheduledAbsoluteLayerBlock_mem_start hp)
  exact hbT.trans_le (hm.trans (d.scheduledAbsoluteLayerBlock_bounds initial m p hp).1)

end GapFamily.Construction.RealTailLocalData
