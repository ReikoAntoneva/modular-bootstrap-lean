import GapFamily.Construction.LayerScheduleRecurrence
import GapFamily.Construction.LayerScheduleIteration

/-! The literal flattened slot execution of every finite layer prefix. -/

noncomputable section
namespace GapFamily.Construction

/-- Every slot in the first `n` layers, retaining its absolute layer index. -/
def scheduledSlotPrefix (T n : ℕ) : List (ℕ × ℤ) :=
  (List.range n).flatMap fun k => (layerSlots (T + k)).map fun j => (T + k, j)

@[simp] theorem scheduledSlotPrefix_zero (T : ℕ) : scheduledSlotPrefix T 0 = [] := rfl

theorem scheduledSlotPrefix_succ (T n : ℕ) :
    scheduledSlotPrefix T (n + 1) = scheduledSlotPrefix T n ++
      (layerSlots (T + n)).map (fun j => (T + n, j)) := by
  simp [scheduledSlotPrefix, List.range_succ, List.flatMap_append]

/-- The exact number of prescribed slots in a finite prefix. -/
@[simp] theorem length_scheduledSlotPrefix (T n : ℕ) :
    (scheduledSlotPrefix T n).length = 2 * n * (2 * T + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [scheduledSlotPrefix_succ, List.length_append, List.length_map,
      length_layerSlots, ih]
    ring

/-- Layer recursion is exactly the fold over the literal flattened slot list;
this identity needs no invariant or cell-update hypothesis. -/
theorem layerIteration_eq_scheduledSlotPrefix_fold {S : Type*}
    (T : ℕ) (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S)
    (initial : S) (n : ℕ) :
    layerIteration T (fun m => executeLayer m front (update m)) initial n =
      (scheduledSlotPrefix T n).foldl
        (fun s p => executeSlot p.1 front (update p.1) p.2 s) initial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [layerIteration_succ, scheduledSlotPrefix_succ, List.foldl_append, ← ih,
      List.foldl_map]
    exact executeLayer_eq_slot_fold (T + n) front (update (T + n)) _

end GapFamily.Construction
