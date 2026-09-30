import GapFamily.Construction.LayerScheduleConstruction
import GapFamily.Construction.LayerScheduleBlock

/-!
# Actual node lists of the constructed layer sequence

Every node block uses the literal scheduled slots, the constructed pre-layer
state, and the same skip guard as the actual state update. Local cell contracts
therefore imply the bounds of every node in every finite stage.
-/

noncomputable section
namespace GapFamily.Construction

variable {S : Type*}

/-- The actual emitted list of layer `T+n`, using its constructed initial state.
Skipped slots emit the empty list and every live slot uses its pre-update state. -/
def scheduledLayerBlock (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (n : ℕ) : List (ℝ × ℤ) :=
  layerNodeBlock (executeSlot (T + n) front (update (T + n)))
    (guardedSlotNodes (T + n) front (node (T + n))) (T + n)
    (scheduledLayerState T front update initial n)

/-- The terminal state used for the next block is exactly the state obtained
while emitting this block. -/
theorem scheduledLayerBlock_next_state (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (n : ℕ) :
    slotState (executeSlot (T + n) front (update (T + n))) (layerSlots (T + n))
      (scheduledLayerState T front update initial n) =
        scheduledLayerState T front update initial (n + 1) :=
  (scheduledLayerState_succ_eq_slot_fold T front update initial n).symm

/-- Stage-dependent local update and emission contracts imply all actual node
bounds. The upper cell endpoint is included, as required for closed-cell nodes. -/
theorem scheduledLayerBlock_indexed_bounds (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (P : ℕ → S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) (P m))
    (hroll : ∀ m, T ≤ m → ∀ s, P m s → FrontInvariant (m + 1) front s → P (m + 1) s)
    (hP : P T initial) (hf : FrontInvariant T front initial)
    (hnode : ∀ m, T ≤ m → ∀ s j, P m s → CanExecute m front s j →
      ∀ p ∈ node m j s, front s j ≤ p.1 ∧ p.1 ≤ front s j + 1 ∧ p.2 = j) :
    ∀ n, ∀ p ∈ scheduledLayerBlock T front update node initial n,
      ((T + n : ℕ) : ℝ) ≤ p.1 ∧ p.1 < ((T + n : ℕ) : ℝ) + 2 ∧
        |(p.2 : ℝ)| ≤ p.1 := by
  intro n
  have hm : T ≤ T + n := Nat.le_add_right _ _
  have hi := scheduledLayerState_indexed_invariant T front update initial P C hroll hP hf n
  unfold scheduledLayerBlock
  refine layerNodeBlock_guarded_bounds
    (P := fun s => P (T + n) s ∧ FrontInvariant (T + n) front s) hi ?_ ?_ ?_
  · intro j hj s hs
    exact executeSlot_invariant (C (T + n) hm) hs.1 hs.2 hj
  · intro j _ s hs
    exact (le_max_left _ _).trans (hs.2 j)
  · intro j hj s hs hactive
    exact hnode (T + n) hm s j hs.1
      ⟨hj, (le_max_left _ _).trans (hs.2 j), hactive⟩

/-- Uniform local contracts suffice to prove every actual layer-node bound;
there is no premise about a complete layer or its final emitted list. -/
theorem scheduledLayerBlock_bounds (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (P : S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
    (hP : P initial) (hf : FrontInvariant T front initial)
    (hnode : ∀ m, T ≤ m → ∀ s j, P s → CanExecute m front s j →
      ∀ p ∈ node m j s, front s j ≤ p.1 ∧ p.1 ≤ front s j + 1 ∧ p.2 = j) :
    ∀ n, ∀ p ∈ scheduledLayerBlock T front update node initial n,
      ((T + n : ℕ) : ℝ) ≤ p.1 ∧ p.1 < ((T + n : ℕ) : ℝ) + 2 ∧
        |(p.2 : ℝ)| ≤ p.1 :=
  scheduledLayerBlock_indexed_bounds T front update node initial (fun _ => P) C
    (fun _ _ _ hs _ => hs) hP hf hnode

/-- Absolute indexing of the same emitted lists, with empty layers before the
starting layer. This is the literal list family consumed by the spectrum. -/
def scheduledAbsoluteLayerBlock (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (m : ℕ) : List (ℝ × ℤ) :=
  if T ≤ m then scheduledLayerBlock T front update node initial (m - T) else []

@[simp] theorem scheduledAbsoluteLayerBlock_add (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (n : ℕ) :
    scheduledAbsoluteLayerBlock T front update node initial (T + n) =
      scheduledLayerBlock T front update node initial n := by
  simp [scheduledAbsoluteLayerBlock]

/-- Reindexing preserves the actual absolute-layer bounds needed for local finiteness. -/
theorem scheduledAbsoluteLayerBlock_bounds (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (P : S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
    (hP : P initial) (hf : FrontInvariant T front initial)
    (hnode : ∀ m, T ≤ m → ∀ s j, P s → CanExecute m front s j →
      ∀ p ∈ node m j s, front s j ≤ p.1 ∧ p.1 ≤ front s j + 1 ∧ p.2 = j) :
    ∀ m, ∀ p ∈ scheduledAbsoluteLayerBlock T front update node initial m,
      (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2 ∧ |(p.2 : ℝ)| ≤ p.1 := by
  intro m p hp
  unfold scheduledAbsoluteLayerBlock at hp
  split_ifs at hp with hm
  · have h := scheduledLayerBlock_bounds T front update node initial P C hP hf hnode
      (m - T) p hp
    simpa only [Nat.add_sub_of_le hm] using h
  · simp at hp

/-- Every occurrence in the absolute layer family belongs to a layer at or
above the start; earlier list blocks are literally empty. -/
theorem scheduledAbsoluteLayerBlock_mem_start {T : ℕ} {front : S → ℤ → ℝ}
    {update : ℕ → ℤ → S → S} {node : ℕ → ℤ → S → List (ℝ × ℤ)}
    {initial : S} {m : ℕ} {p : ℝ × ℤ}
    (hp : p ∈ scheduledAbsoluteLayerBlock T front update node initial m) : T ≤ m := by
  by_contra h
  simp [scheduledAbsoluteLayerBlock, h] at hp

/-- The absolute literal lists satisfy the full spectrum input bounds whenever
the fixed physical minimum lies below the starting frontier. -/
theorem scheduledAbsoluteLayerBlock_spectrum_bounds (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (P : S → Prop) (b : ℝ) (hb : b ≤ (T : ℝ))
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
    (hP : P initial) (hf : FrontInvariant T front initial)
    (hnode : ∀ m, T ≤ m → ∀ s j, P s → CanExecute m front s j →
      ∀ p ∈ node m j s, front s j ≤ p.1 ∧ p.1 ≤ front s j + 1 ∧ p.2 = j) :
    ∀ m, ∀ p ∈ scheduledAbsoluteLayerBlock T front update node initial m,
      b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1 ∧ (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2 := by
  intro m p hp
  have hm : (T : ℝ) ≤ (m : ℝ) :=
    Nat.cast_le.mpr (scheduledAbsoluteLayerBlock_mem_start hp)
  obtain ⟨hlo, hhi, hphysical⟩ :=
    scheduledAbsoluteLayerBlock_bounds T front update node initial P C hP hf hnode m p hp
  exact ⟨hb.trans (hm.trans hlo), hphysical, hlo, hhi⟩

/-- The finite permanent atom list after `n` actual layers. -/
def scheduledNodePrefix (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (initialAtoms : List (ℝ × ℤ)) (n : ℕ) : List (ℝ × ℤ) :=
  atomBlockPrefix initialAtoms (scheduledLayerBlock T front update node initial) n

@[simp] theorem scheduledNodePrefix_zero (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (initialAtoms : List (ℝ × ℤ)) :
    scheduledNodePrefix T front update node initial initialAtoms 0 = initialAtoms :=
  atomBlockPrefix_zero _ _

@[simp] theorem scheduledNodePrefix_succ (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (initialAtoms : List (ℝ × ℤ)) (n : ℕ) :
    scheduledNodePrefix T front update node initial initialAtoms (n + 1) =
      scheduledNodePrefix T front update node initial initialAtoms n ++
        scheduledLayerBlock T front update node initial n :=
  atomBlockPrefix_succ _ _ _

/-- Every earlier actual atom occurrence remains an ordered prefix. -/
theorem scheduledNodePrefix_isPrefix (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (initialAtoms : List (ℝ × ℤ)) {n k : ℕ} (hnk : n ≤ k) :
    scheduledNodePrefix T front update node initial initialAtoms n <+:
      scheduledNodePrefix T front update node initial initialAtoms k :=
  atomBlockPrefix_isPrefix _ _ hnk

theorem scheduledNodePrefix_sublist (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (initialAtoms : List (ℝ × ℤ)) {n k : ℕ} (hnk : n ≤ k) :
    (scheduledNodePrefix T front update node initial initialAtoms n).Sublist
      (scheduledNodePrefix T front update node initial initialAtoms k) :=
  (scheduledNodePrefix_isPrefix T front update node initial initialAtoms hnk).sublist

/-- Once the advancing layer exceeds a cutoff, all later finite states have
exactly the same atom list below that cutoff, with every multiplicity retained. -/
theorem scheduledNodePrefix_sublevel (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (initialAtoms : List (ℝ × ℤ)) (P : S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
    (hP : P initial) (hf : FrontInvariant T front initial)
    (hnode : ∀ m, T ≤ m → ∀ s j, P s → CanExecute m front s j →
      ∀ p ∈ node m j s, front s j ≤ p.1 ∧ p.1 ≤ front s j + 1 ∧ p.2 = j)
    (D : ℝ) {n k : ℕ} (hnk : n ≤ k) (hD : D < ((T + n : ℕ) : ℝ)) :
    atomSublevel D (scheduledNodePrefix T front update node initial initialAtoms k) =
      atomSublevel D (scheduledNodePrefix T front update node initial initialAtoms n) := by
  apply atomSublevel_atomBlockPrefix_eq_of_layer_lower D initialAtoms _ T hnk hD
  intro r p hp
  exact (scheduledLayerBlock_bounds T front update node initial P C hP hf hnode r p hp).1

/-- Every fixed finite cutoff becomes permanently constant in the actual node sequence. -/
theorem scheduledNodePrefix_eventually_sublevel (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (initialAtoms : List (ℝ × ℤ)) (P : S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
    (hP : P initial) (hf : FrontInvariant T front initial)
    (hnode : ∀ m, T ≤ m → ∀ s j, P s → CanExecute m front s j →
      ∀ p ∈ node m j s, front s j ≤ p.1 ∧ p.1 ≤ front s j + 1 ∧ p.2 = j)
    (D : ℝ) :
    ∃ n : ℕ, ∀ k, n ≤ k →
      atomSublevel D (scheduledNodePrefix T front update node initial initialAtoms k) =
        atomSublevel D (scheduledNodePrefix T front update node initial initialAtoms n) := by
  apply atomSublevel_atomBlockPrefix_eventually_constant D initialAtoms _ T
  intro r p hp
  exact (scheduledLayerBlock_bounds T front update node initial P C hP hf hnode r p hp).1

/-- Every additive contribution of an already completed energy sublevel is
permanent in the actual finite node sequence. -/
theorem scheduledNodePrefix_sublevel_sum {A : Type*} [AddCommMonoid A]
    (T : ℕ) (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S)
    (node : ℕ → ℤ → S → List (ℝ × ℤ)) (initial : S)
    (initialAtoms : List (ℝ × ℤ)) (P : S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
    (hP : P initial) (hf : FrontInvariant T front initial)
    (hnode : ∀ m, T ≤ m → ∀ s j, P s → CanExecute m front s j →
      ∀ p ∈ node m j s, front s j ≤ p.1 ∧ p.1 ≤ front s j + 1 ∧ p.2 = j)
    (D : ℝ) {n k : ℕ} (hnk : n ≤ k) (hD : D < ((T + n : ℕ) : ℝ))
    (f : ℝ × ℤ → A) :
    ((atomSublevel D (scheduledNodePrefix T front update node initial initialAtoms k)).map f).sum =
      ((atomSublevel D (scheduledNodePrefix T front update node initial initialAtoms n)).map f).sum := by
  rw [scheduledNodePrefix_sublevel T front update node initial initialAtoms P C hP hf hnode
    D hnk hD]

/-- The actual finite prefix, including the initial atoms, lies below the
explicit common cutoff at its next layer. -/
theorem scheduledNodePrefix_lt_layerCutoff (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (node : ℕ → ℤ → S → List (ℝ × ℤ))
    (initial : S) (initialAtoms : List (ℝ × ℤ)) (P : S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
    (hP : P initial) (hf : FrontInvariant T front initial)
    (hnode : ∀ m, T ≤ m → ∀ s j, P s → CanExecute m front s j →
      ∀ p ∈ node m j s, front s j ≤ p.1 ∧ p.1 ≤ front s j + 1 ∧ p.2 = j)
    (U : ℝ) (hU : 0 ≤ U) (hinitial : ∀ p ∈ initialAtoms, p.1 ≤ U + 1) (n : ℕ) :
    ∀ p ∈ scheduledNodePrefix T front update node initial initialAtoms n,
      p.1 < layerCutoff U (T + n) := by
  intro p hp
  obtain hp | ⟨r, hr, hp⟩ := mem_atomBlockPrefix.mp hp
  · exact lt_layerCutoff_of_initial_upper (hinitial p hp)
  · apply lt_layerCutoff_of_prior_layer_upper hU (Nat.add_le_add_left (Nat.le_of_lt hr) T)
    exact (scheduledLayerBlock_bounds T front update node initial P C hP hf hnode r p hp).2.1

end GapFamily.Construction
