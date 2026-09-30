import GapFamily.Construction.LayerScheduleNode
import GapFamily.Construction.PermanentSpectrumList
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Thermal summability passes from the actual finite cell lists to the
literal scheduled layer lists. Flattening preserves every repeated node
occurrence and uses each slot's actual pre-update state.
-/

noncomputable section

namespace GapFamily.Construction

/-- The ordinary thermal sum over a list, with each occurrence counted once. -/
def nodeListThermal (t : ℝ) (nodes : List (ℝ × ℤ)) : ℝ :=
  (nodes.map (fun p => Real.exp (-t * p.1))).sum

@[simp] theorem nodeListThermal_nil (t : ℝ) : nodeListThermal t [] = 0 := rfl

theorem nodeListThermal_nonneg (t : ℝ) (nodes : List (ℝ × ℤ)) :
    0 ≤ nodeListThermal t nodes := by
  unfold nodeListThermal
  apply List.sum_nonneg
  intro r hr
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
  exact (Real.exp_pos _).le

/-- Only active cells need a summability proof when every other actual
emission is the empty list. The subtype records cells, not distinct coordinates.
-/
theorem summable_nodeListThermal_of_active {ι : Type*}
    (active : ι → Prop) (node : ι → List (ℝ × ℤ)) (t : ℝ)
    (hzero : ∀ i, ¬active i → node i = [])
    (hsum : Summable (fun i : {i // active i} => nodeListThermal t (node i))) :
    Summable (fun i => nodeListThermal t (node i)) := by
  classical
  apply ((summable_subtype_iff_indicator (s := {i | active i})
    (f := fun i => nodeListThermal t (node i))).mp hsum).congr
  intro i
  by_cases hi : active i
  · simp [Set.indicator, hi]
  · simp [Set.indicator, hi, hzero i hi]

/-- Literal recursive emission equals flattening the indexed cell emissions
from their actual prefix states. No node coordinates are deduplicated. -/
theorem slotNodeBlock_eq_flatten_ofFn {S : Type*} (step : ℤ → S → S)
    (node : ℤ → S → List (ℝ × ℤ)) (slots : List ℤ) (s : S) :
    slotNodeBlock step node slots s =
      (List.ofFn (fun q : Fin slots.length =>
        node (slots.get q) (slotState step (slots.take q.val) s))).flatten := by
  induction slots generalizing s with
  | nil => simp
  | cons j js ih =>
      simp only [slotNodeBlock_cons, List.length_cons, List.ofFn_succ, List.flatten_cons]
      simpa [List.take_succ_cons, slotState] using congrArg (node j s ++ ·) (ih (step j s))

/-- Every additive list sum respects the same finite flattening. -/
theorem sum_flatten_ofFn {α A : Type*} [AddCommMonoid A] {n : ℕ}
    (cell : Fin n → List α) (f : α → A) :
    (((List.ofFn cell).flatten).map f).sum = ∑ q : Fin n, ((cell q).map f).sum := by
  simp [List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn]

theorem nodeListThermal_flatten_ofFn (t : ℝ) {n : ℕ}
    (cell : Fin n → List (ℝ × ℤ)) :
    nodeListThermal t (List.ofFn cell).flatten = ∑ q : Fin n, nodeListThermal t (cell q) :=
  sum_flatten_ofFn cell (fun p => Real.exp (-t * p.1))

/-- The finite list emitted at every layer by a sigma-indexed cell family. -/
def cellLayerList (cellCount : ℕ → ℕ)
    (cell : ∀ m, Fin (cellCount m) → List (ℝ × ℤ)) (m : ℕ) : List (ℝ × ℤ) :=
  (List.ofFn (cell m)).flatten

theorem cellLayerList_thermal_eq (cellCount : ℕ → ℕ)
    (cell : ∀ m, Fin (cellCount m) → List (ℝ × ℤ)) (t : ℝ) (m : ℕ) :
    nodeListThermal t (cellLayerList cellCount cell m) =
      ∑ q : Fin (cellCount m), nodeListThermal t (cell m q) :=
  nodeListThermal_flatten_ofFn t (cell m)

theorem summable_cellLayerList_thermal (cellCount : ℕ → ℕ)
    (cell : ∀ m, Fin (cellCount m) → List (ℝ × ℤ)) (t : ℝ)
    (hsum : Summable (fun p : Σ m, Fin (cellCount m) => nodeListThermal t (cell p.1 p.2))) :
    Summable (fun m => nodeListThermal t (cellLayerList cellCount cell m)) := by
  simpa only [cellLayerList_thermal_eq, tsum_fintype] using hsum.sigma

theorem tsum_cellLayerList_thermal (cellCount : ℕ → ℕ)
    (cell : ∀ m, Fin (cellCount m) → List (ℝ × ℤ)) (t : ℝ)
    (hsum : Summable (fun p : Σ m, Fin (cellCount m) => nodeListThermal t (cell p.1 p.2))) :
    (∑' m, nodeListThermal t (cellLayerList cellCount cell m)) =
      ∑' p : Σ m, Fin (cellCount m), nodeListThermal t (cell p.1 p.2) := by
  simpa only [cellLayerList_thermal_eq, tsum_fintype] using
    (Summable.tsum_sigma' (fun _ => Summable.of_finite) hsum).symm

/-- The actual guarded emission from a relative scheduled slot. Its index
agrees with the chronological slot family, including skipped slots. -/
def scheduledSlotNodeList {S : Type*} (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (p : Σ n : ℕ, Fin (layerSlots (T + n)).length) : List (ℝ × ℤ) :=
  guardedSlotNodes (T + p.1) front (node (T + p.1)) ((layerSlots (T + p.1)).get p.2)
    (slotState (executeSlot (T + p.1) front (update (T + p.1)))
      ((layerSlots (T + p.1)).take p.2.val)
      (scheduledLayerState T front update initial p.1))

theorem scheduledLayerBlock_eq_flatten_ofFn {S : Type*}
    (T : ℕ) (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S)
    (node : ℕ → ℤ → S → List (ℝ × ℤ)) (initial : S) (n : ℕ) :
    scheduledLayerBlock T front update node initial n =
      (List.ofFn (fun q : Fin (layerSlots (T + n)).length =>
        scheduledSlotNodeList T front update node initial ⟨n, q⟩)).flatten :=
  slotNodeBlock_eq_flatten_ofFn _ _ _ _

theorem scheduledLayerBlock_thermal_eq {S : Type*}
    (T : ℕ) (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S)
    (node : ℕ → ℤ → S → List (ℝ × ℤ)) (initial : S) (t : ℝ) (n : ℕ) :
    nodeListThermal t (scheduledLayerBlock T front update node initial n) =
      ∑ q : Fin (layerSlots (T + n)).length,
        nodeListThermal t (scheduledSlotNodeList T front update node initial ⟨n, q⟩) := by
  rw [scheduledLayerBlock_eq_flatten_ofFn, nodeListThermal_flatten_ofFn]

/-- Summing the actual finite cell emissions gives summability of the
literal layer lists; no bound on the number of cells is required. -/
theorem summable_scheduledLayerBlock_thermal {S : Type*}
    (T : ℕ) (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S)
    (node : ℕ → ℤ → S → List (ℝ × ℤ)) (initial : S) (t : ℝ)
    (hsum : Summable (fun p : Σ n : ℕ, Fin (layerSlots (T + n)).length =>
      nodeListThermal t (scheduledSlotNodeList T front update node initial p))) :
    Summable (fun n => nodeListThermal t (scheduledLayerBlock T front update node initial n)) := by
  simpa only [scheduledLayerBlock_thermal_eq, tsum_fintype] using hsum.sigma

/-- The complete scheduled layer sum equals the sum over the same actual
slot occurrences. -/
theorem tsum_scheduledLayerBlock_thermal {S : Type*}
    (T : ℕ) (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S)
    (node : ℕ → ℤ → S → List (ℝ × ℤ)) (initial : S) (t : ℝ)
    (hsum : Summable (fun p : Σ n : ℕ, Fin (layerSlots (T + n)).length =>
      nodeListThermal t (scheduledSlotNodeList T front update node initial p))) :
    (∑' n, nodeListThermal t (scheduledLayerBlock T front update node initial n)) =
      ∑' p : Σ n : ℕ, Fin (layerSlots (T + n)).length,
        nodeListThermal t (scheduledSlotNodeList T front update node initial p) := by
  simpa only [scheduledLayerBlock_thermal_eq, tsum_fintype] using
    (Summable.tsum_sigma' (fun _ => Summable.of_finite) hsum).symm

/-- Selected active cell masses control the literal scheduled layer lists;
all skipped or invalid slots are zero because their actual emission is empty. -/
theorem summable_scheduledLayerBlock_thermal_of_active {S : Type*}
    (T : ℕ) (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S)
    (node : ℕ → ℤ → S → List (ℝ × ℤ)) (initial : S) (t : ℝ)
    (active : (Σ n : ℕ, Fin (layerSlots (T + n)).length) → Prop)
    (hzero : ∀ p, ¬active p → scheduledSlotNodeList T front update node initial p = [])
    (hsum : Summable (fun p : {p // active p} =>
      nodeListThermal t (scheduledSlotNodeList T front update node initial p))) :
    Summable (fun n => nodeListThermal t (scheduledLayerBlock T front update node initial n)) :=
  summable_scheduledLayerBlock_thermal T front update node initial t
    (summable_nodeListThermal_of_active active _ t hzero hsum)

/-- The actual empty layers before `T` do not affect thermal summability. -/
theorem summable_scheduledAbsoluteLayerBlock_thermal {S : Type*}
    (T : ℕ) (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S)
    (node : ℕ → ℤ → S → List (ℝ × ℤ)) (initial : S) (t : ℝ)
    (hsum : Summable (fun p : Σ n : ℕ, Fin (layerSlots (T + n)).length =>
      nodeListThermal t (scheduledSlotNodeList T front update node initial p))) :
    Summable (fun m => nodeListThermal t
      (scheduledAbsoluteLayerBlock T front update node initial m)) := by
  apply (summable_nat_add_iff T).mp
  simpa only [Nat.add_comm, scheduledAbsoluteLayerBlock_add] using
    summable_scheduledLayerBlock_thermal T front update node initial t hsum

end GapFamily.Construction
