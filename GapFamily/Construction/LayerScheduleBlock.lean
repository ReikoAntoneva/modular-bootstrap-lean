import GapFamily.Construction.LayerSchedule
import GapFamily.Construction.LayerBlockPermanence
import Mathlib.Data.List.Infix

/-!
# Finite emitted blocks along the literal slot execution

Each emission uses the state immediately before its slot update. All emitted
nodes are retained in a finite list, including repeated coordinates. Slot
invariants propagate by finite recursion and imply bounds on every emitted node.
-/

noncomputable section
namespace GapFamily.Construction

/-- Execute a finite list of integer-spin slots from left to right. -/
def slotState {S : Type*} (step : ℤ → S → S) (slots : List ℤ) (s : S) : S :=
  slots.foldl (fun s j => step j s) s

/-- Each block is emitted from its literal pre-update state and appended in order. -/
def slotNodeBlock {S : Type*} (step : ℤ → S → S)
    (node : ℤ → S → List (ℝ × ℤ)) : List ℤ → S → List (ℝ × ℤ)
  | [], _ => []
  | j :: js, s => node j s ++ slotNodeBlock step node js (step j s)

@[simp] theorem slotState_nil {S : Type*} (step : ℤ → S → S) (s : S) :
    slotState step [] s = s := rfl

@[simp] theorem slotState_cons {S : Type*} (step : ℤ → S → S)
    (j : ℤ) (js : List ℤ) (s : S) :
    slotState step (j :: js) s = slotState step js (step j s) := rfl

@[simp] theorem slotNodeBlock_nil {S : Type*} (step : ℤ → S → S)
    (node : ℤ → S → List (ℝ × ℤ)) (s : S) : slotNodeBlock step node [] s = [] := rfl

@[simp] theorem slotNodeBlock_cons {S : Type*} (step : ℤ → S → S)
    (node : ℤ → S → List (ℝ × ℤ)) (j : ℤ) (js : List ℤ) (s : S) :
    slotNodeBlock step node (j :: js) s = node j s ++ slotNodeBlock step node js (step j s) := rfl

theorem slotState_append {S : Type*} (step : ℤ → S → S)
    (left right : List ℤ) (s : S) :
    slotState step (left ++ right) s = slotState step right (slotState step left s) := by
  exact List.foldl_append

/-- Splitting a slot list records the actual state passed from the first block
into the second; no independently chosen terminal state is involved. -/
theorem slotNodeBlock_append {S : Type*} (step : ℤ → S → S)
    (node : ℤ → S → List (ℝ × ℤ)) (left right : List ℤ) (s : S) :
    slotNodeBlock step node (left ++ right) s =
      slotNodeBlock step node left s ++ slotNodeBlock step node right (slotState step left s) := by
  induction left generalizing s with
  | nil => simp
  | cons j js ih => simp [ih, List.append_assoc]

/-- A slot invariant propagates through every literal intermediate state. -/
theorem slotState_invariant {S : Type*} {step : ℤ → S → S} {P : S → Prop}
    {slots : List ℤ} {s : S} (hs : P s)
    (hstep : ∀ j ∈ slots, ∀ t, P t → P (step j t)) :
    P (slotState step slots s) := by
  induction slots generalizing s with
  | nil => exact hs
  | cons j js ih =>
      exact ih (hstep j (by simp) s hs)
        (fun i hi t ht => hstep i (by simp [hi]) t ht)

/-- Node membership identifies an actual slot and its literal reachable pre-state. -/
theorem mem_slotNodeBlock_iff {S : Type*} (step : ℤ → S → S)
    (node : ℤ → S → List (ℝ × ℤ)) (slots : List ℤ) (s : S) (p : ℝ × ℤ) :
    p ∈ slotNodeBlock step node slots s ↔
      ∃ left j right, slots = left ++ j :: right ∧ p ∈ node j (slotState step left s) := by
  induction slots generalizing s with
  | nil => simp
  | cons j js ih =>
      simp only [slotNodeBlock_cons, List.mem_append, ih]
      constructor
      · intro hp
        rcases hp with hp | ⟨left, i, right, heq, hp⟩
        · exact ⟨[], j, js, rfl, hp⟩
        · refine ⟨j :: left, i, right, ?_, hp⟩
          simp [heq]
      · rintro ⟨left, i, right, heq, hp⟩
        cases left with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact Or.inl hp
        | cons k ks =>
            simp only [List.cons_append, List.cons.injEq] at heq
            obtain ⟨rfl, heq⟩ := heq
            exact Or.inr ⟨ks, i, right, heq, hp⟩

/-- Any emission property valid at invariant states holds throughout the executed list. -/
theorem slotNodeBlock_property {S : Type*} {step : ℤ → S → S}
    {node : ℤ → S → List (ℝ × ℤ)} {P : S → Prop} {Q : ℝ × ℤ → Prop}
    {slots : List ℤ} {s : S} (hs : P s)
    (hstep : ∀ j ∈ slots, ∀ t, P t → P (step j t))
    (hnode : ∀ j ∈ slots, ∀ t, P t → ∀ p ∈ node j t, Q p) :
    ∀ p ∈ slotNodeBlock step node slots s, Q p := by
  induction slots generalizing s with
  | nil => simp
  | cons j js ih =>
      intro p hp
      simp only [slotNodeBlock_cons, List.mem_append] at hp
      rcases hp with hp | hp
      · exact hnode j (by simp) s hs p hp
      · exact ih (hstep j (by simp) s hs)
          (fun i hi t ht => hstep i (by simp [hi]) t ht)
          (fun i hi t ht q hq => hnode i (by simp [hi]) t ht q hq) p hp

/-- The empty emission convention implements a guarded skipped slot. -/
def guardedSlotNodes {S : Type*} (m : ℕ) (front : S → ℤ → ℝ)
    (node : ℤ → S → List (ℝ × ℤ)) (j : ℤ) (s : S) : List (ℝ × ℤ) :=
  if (m : ℝ) + 1 ≤ front s j then [] else node j s

theorem guardedSlotNodes_eq_nil {S : Type*} (m : ℕ) (front : S → ℤ → ℝ)
    (node : ℤ → S → List (ℝ × ℤ)) (j : ℤ) (s : S)
    (hskip : (m : ℝ) + 1 ≤ front s j) : guardedSlotNodes m front node j s = [] := by
  simp [guardedSlotNodes, hskip]

theorem mem_guardedSlotNodes_iff {S : Type*} (m : ℕ) (front : S → ℤ → ℝ)
    (node : ℤ → S → List (ℝ × ℤ)) (j : ℤ) (s : S) (p : ℝ × ℤ) :
    p ∈ guardedSlotNodes m front node j s ↔
      front s j < (m : ℝ) + 1 ∧ p ∈ node j s := by
  simp only [guardedSlotNodes]
  split_ifs with h
  · simp [not_lt_of_ge h]
  · simp [lt_of_not_ge h]

/-- The finite node list emitted by the literal two-slot-per-row layer schedule. -/
def layerNodeBlock {S : Type*} (step : ℤ → S → S)
    (node : ℤ → S → List (ℝ × ℤ)) (m : ℕ) (s : S) : List (ℝ × ℤ) :=
  slotNodeBlock step node (layerSlots m) s

/-- Layer emission properties follow from invariants at actual intermediate states. -/
theorem layerNodeBlock_property {S : Type*} {step : ℤ → S → S}
    {node : ℤ → S → List (ℝ × ℤ)} {P : S → Prop} {Q : ℝ × ℤ → Prop}
    {m : ℕ} {s : S} (hs : P s)
    (hstep : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ t, P t → P (step j t))
    (hnode : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ t, P t → ∀ p ∈ node j t, Q p) :
    ∀ p ∈ layerNodeBlock step node m s, Q p :=
  slotNodeBlock_property hs
    (fun j hj => hstep j ((mem_layerSlots m j).mp hj))
    (fun j hj => hnode j ((mem_layerSlots m j).mp hj))

/-- In particular the layer is a finite actual list with the claimed energy and
physical-spin bounds, without a separately chosen layer count. -/
theorem layerNodeBlock_bounds {S : Type*} {step : ℤ → S → S}
    {node : ℤ → S → List (ℝ × ℤ)} {P : S → Prop}
    {m : ℕ} {s : S} (hs : P s)
    (hstep : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ t, P t → P (step j t))
    (hnode : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ t, P t → ∀ p ∈ node j t,
      (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2 ∧ |(p.2 : ℝ)| ≤ p.1) :
    ∀ p ∈ layerNodeBlock step node m s,
      (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2 ∧ |(p.2 : ℝ)| ≤ p.1 :=
  layerNodeBlock_property hs hstep hnode

/-- Guarded emissions inherit the layer bound from their live front. The guard
supplies the upper front bound, while the actual visited-spin range supplies
physicality. -/
theorem layerNodeBlock_guarded_bounds {S : Type*} {step : ℤ → S → S}
    {node : ℤ → S → List (ℝ × ℤ)} {P : S → Prop} {front : S → ℤ → ℝ}
    {m : ℕ} {s : S} (hs : P s)
    (hstep : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ t, P t → P (step j t))
    (hfront : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ t, P t → (m : ℝ) ≤ front t j)
    (hnode : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ t, P t →
      front t j < (m : ℝ) + 1 → ∀ p ∈ node j t,
        front t j ≤ p.1 ∧ p.1 ≤ front t j + 1 ∧ p.2 = j) :
    ∀ p ∈ layerNodeBlock step (guardedSlotNodes m front node) m s,
      (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2 ∧ |(p.2 : ℝ)| ≤ p.1 := by
  refine layerNodeBlock_property (node := guardedSlotNodes m front node)
    (Q := fun p => (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2 ∧ |(p.2 : ℝ)| ≤ p.1)
    hs hstep ?_
  intro j hj t ht p hp
  obtain ⟨hactive, hp⟩ := (mem_guardedSlotNodes_iff m front node j t p).mp hp
  obtain ⟨hlo, hhi, hspin⟩ := hnode j hj t ht hactive p hp
  have hm := hfront j hj t ht
  have hphysical : |(j : ℝ)| ≤ (m : ℝ) := by exact_mod_cast hj
  refine ⟨hm.trans hlo, by linarith, ?_⟩
  rw [hspin]
  exact hphysical.trans (hm.trans hlo)

/-- A scheduled block emits no atom in any earlier energy sublevel. -/
theorem atomSublevel_layerNodeBlock_eq_nil {S : Type*} {step : ℤ → S → S}
    {node : ℤ → S → List (ℝ × ℤ)} {P : S → Prop} {D : ℝ} {m : ℕ} {s : S}
    (hD : D < (m : ℝ)) (hs : P s)
    (hstep : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ t, P t → P (step j t))
    (hnode : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ t, P t → ∀ p ∈ node j t,
      (m : ℝ) ≤ p.1) :
    atomSublevel D (layerNodeBlock step node m s) = [] := by
  apply atomSublevel_eq_nil_of_above
  intro p hp
  exact hD.trans_le (layerNodeBlock_property hs hstep hnode p hp)

/-- Appending the actual executed layer leaves the earlier ordered sublevel,
including all multiplicities, exactly unchanged. -/
theorem atomSublevel_append_layerNodeBlock {S : Type*} {step : ℤ → S → S}
    {node : ℤ → S → List (ℝ × ℤ)} {P : S → Prop} {D : ℝ} {m : ℕ} {s : S}
    (old : List (ℝ × ℤ)) (hD : D < (m : ℝ)) (hs : P s)
    (hstep : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ t, P t → P (step j t))
    (hnode : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ t, P t → ∀ p ∈ node j t,
      (m : ℝ) ≤ p.1) :
    atomSublevel D (old ++ layerNodeBlock step node m s) = atomSublevel D old := by
  rw [atomSublevel_append, atomSublevel_layerNodeBlock_eq_nil hD hs hstep hnode,
    List.append_nil]

/-- Every finite succession of literal later layer blocks preserves the earlier
sublevel. Each block may use its own actual initial state and transition. -/
theorem atomSublevel_append_layerNodeBlocks {S : Type*} (D : ℝ)
    (old : List (ℝ × ℤ)) (layers : List ℕ) (step : ℕ → ℤ → S → S)
    (node : ℕ → ℤ → S → List (ℝ × ℤ)) (state : ℕ → S) (P : ℕ → S → Prop)
    (hlayers : ∀ m ∈ layers, D < (m : ℝ))
    (hs : ∀ m ∈ layers, P m (state m))
    (hstep : ∀ m ∈ layers, ∀ j : ℤ, |j| ≤ (m : ℤ) →
      ∀ t, P m t → P m (step m j t))
    (hnode : ∀ m ∈ layers, ∀ j : ℤ, |j| ≤ (m : ℤ) →
      ∀ t, P m t → ∀ p ∈ node m j t, (m : ℝ) ≤ p.1) :
    atomSublevel D (appendAtomBlocks old
      (layers.map (fun m => layerNodeBlock (step m) (node m) m (state m)))) =
      atomSublevel D old := by
  apply atomSublevel_append_layers D old layers _ hlayers
  intro m hm
  exact layerNodeBlock_property (hs m hm) (hstep m hm) (hnode m hm)

/-- All rows used so far share this explicit comparison cutoff. -/
def layerCutoff (U : ℝ) (m : ℕ) : ℝ := U + (m : ℝ) + 4

/-- The current layer's new atoms lie strictly below its explicit cutoff. -/
theorem lt_layerCutoff_of_layer_upper {U E : ℝ} {m : ℕ} (hU : 0 ≤ U)
    (hE : E < (m : ℝ) + 2) : E < layerCutoff U m := by
  dsimp [layerCutoff]
  linarith

/-- The original atoms lie below every later common cutoff. -/
theorem lt_layerCutoff_of_initial_upper {U E : ℝ} {m : ℕ}
    (hE : E ≤ U + 1) : E < layerCutoff U m := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  dsimp [layerCutoff]
  linarith

/-- Every preceding layer, including the current layer, lies below the same cutoff. -/
theorem lt_layerCutoff_of_prior_layer_upper {U E : ℝ} {n m : ℕ}
    (hU : 0 ≤ U) (hnm : n ≤ m) (hE : E < (n : ℝ) + 2) :
    E < layerCutoff U m := by
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  apply lt_layerCutoff_of_layer_upper hU
  linarith

/-- Initial atoms and every preceding finite layer block fit together below the
same explicit cutoff, while their ordered concatenation retains all atoms. -/
theorem appendAtomBlocks_lt_layerCutoff {U : ℝ} {m : ℕ}
    (initial : List (ℝ × ℤ)) (layers : List ℕ) (block : ℕ → List (ℝ × ℤ))
    (hU : 0 ≤ U) (hinitial : ∀ p ∈ initial, p.1 ≤ U + 1)
    (hlayers : ∀ n ∈ layers, n ≤ m)
    (hblock : ∀ n ∈ layers, ∀ p ∈ block n, p.1 < (n : ℝ) + 2) :
    ∀ p ∈ appendAtomBlocks initial (layers.map block), p.1 < layerCutoff U m := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact lt_layerCutoff_of_initial_upper (hinitial p hp)
  · obtain ⟨atoms, hatoms, hp⟩ := List.mem_flatten.mp hp
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hatoms
    exact lt_layerCutoff_of_prior_layer_upper hU (hlayers n hn) (hblock n hn p hp)

end GapFamily.Construction
