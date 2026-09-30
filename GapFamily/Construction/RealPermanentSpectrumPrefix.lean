import GapFamily.Construction.LayerScheduleNode

/-!
# Literal node histories for real-parameter repair states

Appending the raw emitted list in each repair step makes the scheduler's
node prefix exactly the node field of its state. This identity is independent
of the numerical parameter choice and of whether any slot is skipped.
-/

noncomputable section

namespace GapFamily.Construction

variable {S : Type*} (front : S → ℤ → ℝ) (nodes : S → List (ℝ × ℤ))
  (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
  (hnode : ∀ m J state, nodes (update m J state) = nodes state ++ node m J state)

include hnode

theorem scheduledExecuteSlot_nodes (m : ℕ) (J : ℤ) (state : S) :
    nodes (executeSlot m front (update m) J state) = nodes state ++
      guardedSlotNodes m front (node m) J state := by
  unfold executeSlot guardedSlotNodes
  split_ifs
  · simp only [List.append_nil]
  · exact hnode m J state

theorem scheduledSlotState_nodes (m : ℕ) (slots : List ℤ) (state : S) :
    nodes (slotState (executeSlot m front (update m)) slots state) =
      nodes state ++ slotNodeBlock
        (executeSlot m front (update m))
        (guardedSlotNodes m front (node m)) slots state := by
  induction slots generalizing state with
  | nil => simp
  | cons J slots ih =>
      rw [slotState_cons, ih, scheduledExecuteSlot_nodes front nodes update node hnode,
        slotNodeBlock_cons, List.append_assoc]

/-- The state and the permanent spectrum retain precisely the same repeated
node occurrences after every complete layer. -/
theorem scheduledLayerState_nodes (T : ℕ) (initial : S) (k : ℕ) :
    nodes (scheduledLayerState T front update initial k) =
      scheduledNodePrefix T front update node initial (nodes initial) k := by
  induction k with
  | zero => simp only [scheduledLayerState_zero, scheduledNodePrefix_zero]
  | succ k ih =>
      rw [scheduledLayerState_succ_eq_slot_fold]
      change nodes (slotState (executeSlot (T + k) front (update (T + k)))
        (layerSlots (T + k))
        (scheduledLayerState T front update initial k)) = _
      rw [scheduledSlotState_nodes front nodes update node hnode, ih, scheduledNodePrefix_succ]
      rfl

end GapFamily.Construction
