import GapFamily.Construction.LayerSlotFoldMonotonicity

/-! Chronology of the actual finite slots in the natural layer iteration.
Only unconditional monotonicity of the raw one-cell update is needed to order
all row fronts and separate different cells on the same row. -/

noncomputable section
namespace GapFamily.Construction

open Set

variable {S : Type*}

/-- A countable index for every literal slot in every scheduled layer. -/
abbrev LayerSlotIndex (T : ℕ) := Σ n : ℕ, Fin (layerSlots (T + n)).length

namespace LayerSlotIndex

/-- The absolute layer number of a relative slot index. -/
def layer {T : ℕ} (a : LayerSlotIndex T) : ℕ := T + a.1

/-- The row is read directly from the prescribed finite layer schedule. -/
def row {T : ℕ} (a : LayerSlotIndex T) : ℤ := (layerSlots (T + a.1)).get a.2

/-- Strict chronological order: first the relative layer, then the slot. -/
def Before {T : ℕ} (a b : LayerSlotIndex T) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val)

theorem before_or_before {T : ℕ} {a b : LayerSlotIndex T} (hab : a ≠ b) :
    a.Before b ∨ b.Before a := by
  rcases a with ⟨n, a⟩
  rcases b with ⟨m, b⟩
  by_cases hnm : n = m
  · subst m
    have hav : a.val ≠ b.val := fun h => hab (congrArg (Sigma.mk n) (Fin.ext h))
    rcases lt_or_gt_of_ne hav with h | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
  · rcases lt_or_gt_of_ne hnm with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)

end LayerSlotIndex

/-- The literal prefix of one layer, starting at the actual constructed stage. -/
def layerSlotPreState (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (a : LayerSlotIndex T) : S :=
  ((layerSlots (T + a.1)).take a.2.val).foldl
    (fun s j => executeSlot (T + a.1) front (update (T + a.1)) j s)
    (scheduledLayerState T front update initial a.1)

/-- The actual guarded update at a slot, immediately after its literal prefix. -/
def layerSlotPostState (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (a : LayerSlotIndex T) : S :=
  executeSlot (T + a.1) front (update (T + a.1)) a.row
    (layerSlotPreState T front update initial a)

/-- The open cell traversed by this slot. Skipped slots have an empty interval. -/
def layerSlotInterval (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (a : LayerSlotIndex T) : Set ℝ :=
  Ioo (front (layerSlotPreState T front update initial a) a.row)
    (front (layerSlotPostState T front update initial a) a.row)

theorem executeSlot_front_mono_of_update (m : ℕ) (front : S → ℤ → ℝ)
    (update : ℤ → S → S)
    (hmono : ∀ (j : ℤ) (s : S) (i : ℤ), front s i ≤ front (update j s) i)
    (j : ℤ) (s : S) (i : ℤ) :
    front s i ≤ front (executeSlot m front update j s) i := by
  unfold executeSlot
  split_ifs
  · exact le_rfl
  · exact hmono j s i

theorem executeLayer_front_mono_of_update (m : ℕ) (front : S → ℤ → ℝ)
    (update : ℤ → S → S)
    (hmono : ∀ (j : ℤ) (s : S) (i : ℤ), front s i ≤ front (update j s) i)
    (s : S) (i : ℤ) :
    front s i ≤ front (executeLayer m front update s) i := by
  rw [executeLayer_eq_slot_fold]
  exact front_le_foldl front _
    (fun s j i => executeSlot_front_mono_of_update m front update hmono j s i) s _ i

/-- Every actual completed layer is monotone, without any state invariant. -/
theorem scheduledLayerState_front_monotone_of_update (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S)
    (hmono : ∀ (m : ℕ) (j : ℤ) (s : S) (i : ℤ), front s i ≤ front (update m j s) i)
    (i : ℤ) :
    Monotone (fun n => front (scheduledLayerState T front update initial n) i) := by
  apply monotone_nat_of_le_succ
  intro n
  exact executeLayer_front_mono_of_update (T + n) front (update (T + n))
    (hmono (T + n)) _ i

theorem layerSlotPostState_eq_take_succ (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (a : LayerSlotIndex T) :
    layerSlotPostState T front update initial a =
      ((layerSlots (T + a.1)).take (a.2.val + 1)).foldl
        (fun s j => executeSlot (T + a.1) front (update (T + a.1)) j s)
        (scheduledLayerState T front update initial a.1) := by
  exact (foldl_take_succ_eq_step
    (fun s j => executeSlot (T + a.1) front (update (T + a.1)) j s)
    (scheduledLayerState T front update initial a.1) _ a.2.val a.2.isLt).symm

theorem layerSlotPre_front_le_post (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S)
    (hmono : ∀ (m : ℕ) (j : ℤ) (s : S) (i : ℤ), front s i ≤ front (update m j s) i)
    (a : LayerSlotIndex T) (i : ℤ) :
    front (layerSlotPreState T front update initial a) i ≤
      front (layerSlotPostState T front update initial a) i :=
  executeSlot_front_mono_of_update _ _ _ (hmono _) _ _ i

theorem scheduledLayerState_front_le_slotPre (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S)
    (hmono : ∀ (m : ℕ) (j : ℤ) (s : S) (i : ℤ), front s i ≤ front (update m j s) i)
    (a : LayerSlotIndex T) (i : ℤ) :
    front (scheduledLayerState T front update initial a.1) i ≤
      front (layerSlotPreState T front update initial a) i :=
  front_le_foldl front _
    (fun s j i => executeSlot_front_mono_of_update _ _ _ (hmono _) j s i) _ _ i

theorem layerSlotPost_front_le_nextLayer (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S)
    (hmono : ∀ (m : ℕ) (j : ℤ) (s : S) (i : ℤ), front s i ≤ front (update m j s) i)
    (a : LayerSlotIndex T) (i : ℤ) :
    front (layerSlotPostState T front update initial a) i ≤
      front (scheduledLayerState T front update initial (a.1 + 1)) i := by
  rw [layerSlotPostState_eq_take_succ, scheduledLayerState_succ_eq_slot_fold]
  exact front_foldl_take_le front _
    (fun s j i => executeSlot_front_mono_of_update _ _ _ (hmono _) j s i) _ _ _ i

/-- Every row front after an earlier slot is below the same row front before
a later slot, including slots in different layers. -/
theorem layerSlotPost_front_le_pre (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S)
    (hmono : ∀ (m : ℕ) (j : ℤ) (s : S) (i : ℤ), front s i ≤ front (update m j s) i)
    {a b : LayerSlotIndex T} (hab : a.Before b) (i : ℤ) :
    front (layerSlotPostState T front update initial a) i ≤
      front (layerSlotPreState T front update initial b) i := by
  rcases hab with h | ⟨h, hk⟩
  · exact (layerSlotPost_front_le_nextLayer T front update initial hmono a i).trans
      ((scheduledLayerState_front_monotone_of_update T front update initial hmono i
        (Nat.succ_le_of_lt h)).trans
        (scheduledLayerState_front_le_slotPre T front update initial hmono b i))
  · rcases a with ⟨n, a⟩
    rcases b with ⟨m, b⟩
    dsimp only at h hk
    subst m
    rw [layerSlotPostState_eq_take_succ]
    exact front_foldl_take_monotone front _
      (fun s j i => executeSlot_front_mono_of_update _ _ _ (hmono _) j s i)
      _ _ i (Nat.succ_le_of_lt hk)

/-- Open intervals produced by different slots on the same row are disjoint.
This includes inactive slots, whose pre- and post-fronts coincide. -/
theorem layerSlotInterval_pairwise_disjoint (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S)
    (hmono : ∀ (m : ℕ) (j : ℤ) (s : S) (i : ℤ), front s i ≤ front (update m j s) i) :
    Pairwise (fun a b : LayerSlotIndex T => a.row = b.row →
      Disjoint (layerSlotInterval T front update initial a)
        (layerSlotInterval T front update initial b)) := by
  intro a b hne hrow
  rcases LayerSlotIndex.before_or_before hne with hab | hba
  · apply Set.disjoint_left.mpr
    intro e he hf
    have h := layerSlotPost_front_le_pre T front update initial hmono hab a.row
    have he' := he.2
    have hf' : front (layerSlotPreState T front update initial b) a.row < e := by
      simpa only [hrow] using hf.1
    exact (not_lt_of_ge h) (hf'.trans he')
  · apply Set.disjoint_left.mpr
    intro e he hf
    have h := layerSlotPost_front_le_pre T front update initial hmono hba b.row
    have hf' := hf.2
    have he' : front (layerSlotPreState T front update initial a) b.row < e := by
      simpa only [hrow] using he.1
    exact (not_lt_of_ge h) (he'.trans hf')

theorem layerSlotInterval_eq_empty_of_cleared (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (a : LayerSlotIndex T)
    (h : ((T + a.1 : ℕ) : ℝ) + 1 ≤
      front (layerSlotPreState T front update initial a) a.row) :
    layerSlotInterval T front update initial a = ∅ := by
  simp only [layerSlotInterval, layerSlotPostState, executeSlot_of_cleared _ _ _ _ _ h,
    Ioo_self]

theorem layerSlotInterval_eq_empty_of_update_eq (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (a : LayerSlotIndex T)
    (h : update (T + a.1) a.row (layerSlotPreState T front update initial a) =
      layerSlotPreState T front update initial a) :
    layerSlotInterval T front update initial a = ∅ := by
  unfold layerSlotInterval layerSlotPostState executeSlot
  split_ifs <;> simp only [h, Ioo_self]

end GapFamily.Construction
