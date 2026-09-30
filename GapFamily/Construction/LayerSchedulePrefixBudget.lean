import GapFamily.Construction.LayerScheduleConstruction
import Mathlib.Data.List.Infix

/-!
# The literal partial schedule and its finite budget

A partial stage consists of every completed layer followed by a finite take
of the current layer's actual slots. Its membership, execution, and budget
bounds depend only on the concrete lists, without any cell validity premise.
-/

noncomputable section
namespace GapFamily.Construction

open scoped BigOperators

/-- All completed slots followed by the first `r` slots of the current layer. -/
def scheduledPartialSlotPrefix (T n r : ℕ) : List (ℕ × ℤ) :=
  scheduledSlotPrefix T n ++
    ((layerSlots (T + n)).take r).map (fun j => (T + n, j))

@[simp] theorem scheduledPartialSlotPrefix_zero (T n : ℕ) :
    scheduledPartialSlotPrefix T n 0 = scheduledSlotPrefix T n := by
  simp [scheduledPartialSlotPrefix]

/-- The literal partial stage is an ordered prefix of the next complete stage. -/
theorem scheduledPartialSlotPrefix_isPrefix (T n r : ℕ) :
    scheduledPartialSlotPrefix T n r <+: scheduledSlotPrefix T (n + 1) := by
  refine ⟨((layerSlots (T + n)).drop r).map (fun j => (T + n, j)), ?_⟩
  simp [scheduledPartialSlotPrefix, scheduledSlotPrefix_succ,
    List.append_assoc]

/-- Taking the whole current layer gives the next complete prefix literally. -/
theorem scheduledPartialSlotPrefix_full (T n r : ℕ)
    (hr : (layerSlots (T + n)).length ≤ r) :
    scheduledPartialSlotPrefix T n r = scheduledSlotPrefix T (n + 1) := by
  rw [scheduledPartialSlotPrefix, List.take_of_length_le hr, scheduledSlotPrefix_succ]

/-- The exact finite length includes the saturated take of the current layer. -/
theorem length_scheduledPartialSlotPrefix (T n r : ℕ) :
    (scheduledPartialSlotPrefix T n r).length =
      2 * n * (2 * T + n) + min r (4 * (T + n) + 2) := by
  simp [scheduledPartialSlotPrefix]

/-- Every slot of a complete prefix has its actual absolute layer and an
integer spin in that layer's finite range. -/
theorem scheduledSlotPrefix_mem_bounds {T n : ℕ} {p : ℕ × ℤ}
    (hp : p ∈ scheduledSlotPrefix T n) :
    T ≤ p.1 ∧ p.1 < T + n ∧ |p.2| ≤ (p.1 : ℤ) := by
  obtain ⟨k, hk, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  have hkn : k < n := List.mem_range.mp hk
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hkn T, (mem_layerSlots _ _).mp hj⟩

/-- Membership in a partial prefix obeys both absolute-layer bounds and the
physical spin range, independently of the executed states. -/
theorem scheduledPartialSlotPrefix_mem_bounds {T n r : ℕ} {p : ℕ × ℤ}
    (hp : p ∈ scheduledPartialSlotPrefix T n r) :
    T ≤ p.1 ∧ p.1 ≤ T + n ∧ |p.2| ≤ (p.1 : ℤ) := by
  have h := scheduledSlotPrefix_mem_bounds
    ((scheduledPartialSlotPrefix_isPrefix T n r).subset hp)
  exact ⟨h.1, by omega, h.2.2⟩

/-- The same spin bound in the real physical coordinates used by the cell estimates. -/
theorem scheduledPartialSlotPrefix_mem_real_spin {T n r : ℕ} {p : ℕ × ℤ}
    (hp : p ∈ scheduledPartialSlotPrefix T n r) : |(p.2 : ℝ)| ≤ (p.1 : ℝ) := by
  exact_mod_cast (scheduledPartialSlotPrefix_mem_bounds hp).2.2

/-- The flattened prefix executes exactly the first `r` literal current slots
starting from the already constructed complete-layer state. -/
theorem scheduledPartialSlotPrefix_fold {S : Type*}
    (T n r : ℕ) (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S) (initial : S) :
    (scheduledPartialSlotPrefix T n r).foldl
        (fun s p => executeSlot p.1 front (update p.1) p.2 s) initial =
      ((layerSlots (T + n)).take r).foldl
        (fun s j => executeSlot (T + n) front (update (T + n)) j s)
        (scheduledLayerState T front update initial n) := by
  rw [scheduledPartialSlotPrefix, List.foldl_append, List.foldl_map,
    ← scheduledLayerState_eq_slotPrefix_fold]

/-- The partial budget is the completed budget plus exactly the number of
current-layer slots actually present, with no assumed execution bound. -/
theorem sum_scheduledPartialSlotPrefix_slotBudget_eq (T n r : ℕ) :
    ((scheduledPartialSlotPrefix T n r).map (fun p => Layer.slotBudget p.1)).sum =
      ((scheduledSlotPrefix T n).map (fun p => Layer.slotBudget p.1)).sum +
        (min r (4 * (T + n) + 2) : ℕ) * Layer.slotBudget (T + n) := by
  simp [scheduledPartialSlotPrefix, List.map_map, Function.comp_def, nsmul_eq_mul]


/-- The literal flattened list spends precisely the sum of its layer allowances. -/
theorem sum_scheduledSlotPrefix_slotBudget (T n : ℕ) :
    ((scheduledSlotPrefix T n).map (fun p => Layer.slotBudget p.1)).sum =
      ∑ k ∈ Finset.range n, Layer.layerBudget (T + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [scheduledSlotPrefix_succ, List.map_append, List.sum_append, ih,
        Finset.sum_range_succ]
      congr 1
      simpa only [List.map_map, Function.comp_def] using sum_layerSlots_slotBudget (T + n)

/-- The exact shifted telescoping formula holds for the actual full slot prefix. -/
theorem sum_scheduledSlotPrefix_slotBudget_eq (T n : ℕ) :
    ((scheduledSlotPrefix T n).map (fun p => Layer.slotBudget p.1)).sum =
      (1 / 256 : ℝ) * (1 / ((T : ℝ) + 1) - 1 / ((T : ℝ) + n + 1)) := by
  rw [sum_scheduledSlotPrefix_slotBudget, sum_layerBudget_add]

/-- A prefix beginning at layer `T` already has the quantitative tail allowance. -/
theorem sum_scheduledSlotPrefix_slotBudget_le_tail (T n : ℕ) :
    ((scheduledSlotPrefix T n).map (fun p => Layer.slotBudget p.1)).sum ≤
      (1 / 256 : ℝ) / ((T : ℝ) + 1) := by
  rw [sum_scheduledSlotPrefix_slotBudget_eq]
  calc
    (1 / 256 : ℝ) * (1 / ((T : ℝ) + 1) - 1 / ((T : ℝ) + n + 1)) ≤
        (1 / 256 : ℝ) * (1 / ((T : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left (sub_le_self _ _) (by positivity)
      positivity
    _ = _ := by ring

/-- Every finite actual slot prefix costs at most the fixed C9 allowance. -/
theorem sum_scheduledSlotPrefix_slotBudget_le (T n : ℕ) :
    ((scheduledSlotPrefix T n).map (fun p => Layer.slotBudget p.1)).sum ≤ (1 / 256 : ℝ) := by
  apply (sum_scheduledSlotPrefix_slotBudget_le_tail T n).trans
  apply (div_le_iff₀ (by positivity : 0 < (T : ℝ) + 1)).mpr
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  nlinarith

/-- Nonnegative slot allowances make the actual partial budget no larger than
the next complete prefix's exact budget. -/
theorem sum_scheduledPartialSlotPrefix_slotBudget_le_full (T n r : ℕ) :
    ((scheduledPartialSlotPrefix T n r).map (fun p => Layer.slotBudget p.1)).sum ≤
      ((scheduledSlotPrefix T (n + 1)).map (fun p => Layer.slotBudget p.1)).sum := by
  apply ((scheduledPartialSlotPrefix_isPrefix T n r).sublist.map
    (fun p => Layer.slotBudget p.1)).sum_le_sum
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  unfold Layer.slotBudget
  positivity

/-- Every partial actual stage obeys the shifted tail allowance before any
validity property of its cell updates has been proved. -/
theorem sum_scheduledPartialSlotPrefix_slotBudget_le_tail (T n r : ℕ) :
    ((scheduledPartialSlotPrefix T n r).map (fun p => Layer.slotBudget p.1)).sum ≤
      (1 / 256 : ℝ) / ((T : ℝ) + 1) :=
  (sum_scheduledPartialSlotPrefix_slotBudget_le_full T n r).trans
    (sum_scheduledSlotPrefix_slotBudget_le_tail T (n + 1))

/-- The fixed budget applies unconditionally to the exact partial slot list. -/
theorem sum_scheduledPartialSlotPrefix_slotBudget_le (T n r : ℕ) :
    ((scheduledPartialSlotPrefix T n r).map (fun p => Layer.slotBudget p.1)).sum ≤
      (1 / 256 : ℝ) :=
  (sum_scheduledPartialSlotPrefix_slotBudget_le_full T n r).trans
    (sum_scheduledSlotPrefix_slotBudget_le T (n + 1))

end GapFamily.Construction
