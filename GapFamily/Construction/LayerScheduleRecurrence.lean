import GapFamily.Construction.LayerSchedule

/-! The deterministic finite C9 recurrence. A supplied one-cell update is used
only when its row has not yet reached the next integer frontier. The hypotheses
describe that single update; the full layer is constructed by a finite fold. -/

noncomputable section
namespace GapFamily.Construction

variable {S : Type*}

/-- The beginning-of-layer bound includes every integer spin. -/
def FrontInvariant (m : ℕ) (front : S → ℤ → ℝ) (s : S) : Prop :=
  ∀ j : ℤ, max (m : ℝ) |(j : ℝ)| ≤ front s j

/-- The exact local domain in which a scheduled cell is executed. -/
def CanExecute (m : ℕ) (front : S → ℤ → ℝ) (s : S) (j : ℤ) : Prop :=
  |j| ≤ (m : ℤ) ∧ (m : ℝ) ≤ front s j ∧ front s j < (m : ℝ) + 1

/-- Explicit contracts of the supplied one-cell update, before any layer is run. -/
structure LayerCellContract (m : ℕ) (front : S → ℤ → ℝ)
    (update : ℤ → S → S) (P : S → Prop) : Prop where
  preserve : ∀ s j, P s → CanExecute m front s j → P (update j s)
  unchanged : ∀ s j, P s → CanExecute m front s j →
    ∀ i, i ≠ j → front (update j s) i = front s i
  advance : ∀ s j, P s → CanExecute m front s j →
    front s j + 1 / 2 ≤ front (update j s) j

/-- One prescribed slot either skips a cleared row or performs exactly one update. -/
def executeSlot (m : ℕ) (front : S → ℤ → ℝ) (update : ℤ → S → S)
    (j : ℤ) (s : S) : S :=
  if (m : ℝ) + 1 ≤ front s j then s else update j s

@[simp] theorem executeSlot_of_cleared (m : ℕ) (front : S → ℤ → ℝ)
    (update : ℤ → S → S) (j : ℤ) (s : S) (h : (m : ℝ) + 1 ≤ front s j) :
    executeSlot m front update j s = s := ite_eq_left h

@[simp] theorem executeSlot_of_uncleared (m : ℕ) (front : S → ℤ → ℝ)
    (update : ℤ → S → S) (j : ℤ) (s : S) (h : front s j < (m : ℝ) + 1) :
    executeSlot m front update j s = update j s := ite_eq_right (not_le.mpr h)

theorem executeSlot_front_mono {m : ℕ} {front : S → ℤ → ℝ}
    {update : ℤ → S → S} {P : S → Prop} (C : LayerCellContract m front update P)
    {s : S} (hs : P s) (hf : FrontInvariant m front s)
    {j : ℤ} (hj : |j| ≤ (m : ℤ)) (i : ℤ) :
    front s i ≤ front (executeSlot m front update j s) i := by
  unfold executeSlot
  split_ifs with h
  · exact le_rfl
  · have hc : CanExecute m front s j :=
      ⟨hj, (le_max_left _ _).trans (hf j), lt_of_not_ge h⟩
    by_cases hi : i = j
    · subst i
      have ha := C.advance s j hs hc
      linarith
    · rw [C.unchanged s j hs hc i hi]

theorem executeSlot_invariant {m : ℕ} {front : S → ℤ → ℝ}
    {update : ℤ → S → S} {P : S → Prop} (C : LayerCellContract m front update P)
    {s : S} (hs : P s) (hf : FrontInvariant m front s)
    {j : ℤ} (hj : |j| ≤ (m : ℤ)) :
    P (executeSlot m front update j s) ∧
      FrontInvariant m front (executeSlot m front update j s) := by
  constructor
  · unfold executeSlot
    split_ifs with h
    · exact hs
    · exact C.preserve s j hs ⟨hj, (le_max_left _ _).trans (hf j), lt_of_not_ge h⟩
  · intro i
    exact (hf i).trans (executeSlot_front_mono C hs hf hj i)

/-- The two consecutive slots assigned to one row. -/
def executeRow (m : ℕ) (front : S → ℤ → ℝ) (update : ℤ → S → S)
    (j : ℤ) (s : S) : S :=
  executeSlot m front update j (executeSlot m front update j s)

theorem executeRow_invariant {m : ℕ} {front : S → ℤ → ℝ}
    {update : ℤ → S → S} {P : S → Prop} (C : LayerCellContract m front update P)
    {s : S} (hs : P s) (hf : FrontInvariant m front s)
    {j : ℤ} (hj : |j| ≤ (m : ℤ)) :
    P (executeRow m front update j s) ∧
      FrontInvariant m front (executeRow m front update j s) := by
  obtain ⟨hs', hf'⟩ := executeSlot_invariant C hs hf hj
  exact executeSlot_invariant C hs' hf' hj

theorem executeRow_front_mono {m : ℕ} {front : S → ℤ → ℝ}
    {update : ℤ → S → S} {P : S → Prop} (C : LayerCellContract m front update P)
    {s : S} (hs : P s) (hf : FrontInvariant m front s)
    {j : ℤ} (hj : |j| ≤ (m : ℤ)) (i : ℤ) :
    front s i ≤ front (executeRow m front update j s) i := by
  obtain ⟨hs', hf'⟩ := executeSlot_invariant C hs hf hj
  exact (executeSlot_front_mono C hs hf hj i).trans
    (executeSlot_front_mono C hs' hf' hj i)

theorem executeRow_advance {m : ℕ} {front : S → ℤ → ℝ}
    {update : ℤ → S → S} {P : S → Prop} (C : LayerCellContract m front update P)
    {s : S} (hs : P s) (hf : FrontInvariant m front s)
    {j : ℤ} (hj : |j| ≤ (m : ℤ)) :
    (m : ℝ) + 1 ≤ front (executeRow m front update j s) j := by
  by_cases h0 : (m : ℝ) + 1 ≤ front s j
  · simpa only [executeRow, executeSlot_of_cleared _ _ _ _ _ h0] using h0
  have hc : CanExecute m front s j :=
    ⟨hj, (le_max_left _ _).trans (hf j), lt_of_not_ge h0⟩
  have h1 := C.advance s j hs hc
  have hs' := C.preserve s j hs hc
  have hf' := (executeSlot_invariant C hs hf hj).2
  rw [executeSlot_of_uncleared _ _ _ _ _ hc.2.2] at hf'
  unfold executeRow
  rw [executeSlot_of_uncleared _ _ _ _ _ hc.2.2]
  by_cases h2 : (m : ℝ) + 1 ≤ front (update j s) j
  · simpa only [executeSlot_of_cleared _ _ _ _ _ h2] using h2
  · have hc' : CanExecute m front (update j s) j :=
      ⟨hj, (le_max_left _ _).trans (hf' j), lt_of_not_ge h2⟩
    rw [executeSlot_of_uncleared _ _ _ _ _ hc'.2.2]
    have h3 := C.advance (update j s) j hs' hc'
    linarith [hc.2.1]

/-- Ordered row recursion, with exactly two slots in each recursion step. -/
def executeRows (m : ℕ) (front : S → ℤ → ℝ) (update : ℤ → S → S) :
    List ℤ → S → S
  | [], s => s
  | j :: js, s => executeRows m front update js (executeRow m front update j s)

theorem executeRows_eq_slot_fold (m : ℕ) (front : S → ℤ → ℝ)
    (update : ℤ → S → S) (rows : List ℤ) (s : S) :
    executeRows m front update rows s =
      (rows.flatMap (fun j => [j, j])).foldl
        (fun state j => executeSlot m front update j state) s := by
  induction rows generalizing s with
  | nil => rfl
  | cons j js ih => simp only [executeRows, List.flatMap_cons, List.foldl_append,
      List.foldl_cons, List.foldl_nil, ← ih, executeRow]

theorem executeRows_spec {m : ℕ} {front : S → ℤ → ℝ}
    {update : ℤ → S → S} {P : S → Prop} (C : LayerCellContract m front update P)
    (rows : List ℤ) (hrows : ∀ j ∈ rows, |j| ≤ (m : ℤ))
    {s : S} (hs : P s) (hf : FrontInvariant m front s) :
    P (executeRows m front update rows s) ∧
      FrontInvariant m front (executeRows m front update rows s) ∧
      (∀ i, front s i ≤ front (executeRows m front update rows s) i) ∧
      ∀ j ∈ rows, (m : ℝ) + 1 ≤ front (executeRows m front update rows s) j := by
  induction rows generalizing s with
  | nil => exact ⟨hs, hf, fun _ => le_rfl, by simp⟩
  | cons j js ih =>
    have hj := hrows j (by simp)
    obtain ⟨hs', hf'⟩ := executeRow_invariant C hs hf hj
    obtain ⟨hp, hfront, hmono, hadv⟩ :=
      ih (fun i hi => hrows i (List.mem_cons_of_mem j hi)) hs' hf'
    refine ⟨hp, hfront, fun i => (executeRow_front_mono C hs hf hj i).trans (hmono i), ?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (executeRow_advance C hs hf hj).trans (hmono i)
    · exact hadv i hi

/-- The actual finite layer in increasing spin order. -/
def executeLayer (m : ℕ) (front : S → ℤ → ℝ) (update : ℤ → S → S) (s : S) : S :=
  executeRows m front update (layerRows m) s

theorem executeLayer_eq_slot_fold (m : ℕ) (front : S → ℤ → ℝ)
    (update : ℤ → S → S) (s : S) :
    executeLayer m front update s = (layerSlots m).foldl
      (fun state j => executeSlot m front update j state) s :=
  executeRows_eq_slot_fold m front update (layerRows m) s

/-- Every row, including those outside the finite slot list, meets the next
integer frontier after the constructed layer. -/
theorem executeLayer_invariant {m : ℕ} {front : S → ℤ → ℝ}
    {update : ℤ → S → S} {P : S → Prop} (C : LayerCellContract m front update P)
    {s : S} (hs : P s) (hf : FrontInvariant m front s) :
    P (executeLayer m front update s) ∧
      FrontInvariant (m + 1) front (executeLayer m front update s) := by
  obtain ⟨hp, hfront, hmono, hadv⟩ := executeRows_spec C (layerRows m)
    (fun j hj => (mem_layerRows.mp hj)) hs hf
  refine ⟨hp, ?_⟩
  intro j
  apply max_le
  · have h : (m : ℝ) + 1 ≤ front (executeLayer m front update s) j := by
      by_cases hj : |j| ≤ (m : ℤ)
      · exact hadv j (mem_layerRows.mpr hj)
      · have hInt : (m : ℤ) + 1 ≤ |j| := by omega
        have hReal : (m : ℝ) + 1 ≤ |(j : ℝ)| := by exact_mod_cast hInt
        exact hReal.trans ((le_max_right _ _).trans (hfront j))
    simpa only [Nat.cast_add, Nat.cast_one] using h
  · exact (le_max_right _ _).trans (hfront j)

theorem executeLayer_front_mono {m : ℕ} {front : S → ℤ → ℝ}
    {update : ℤ → S → S} {P : S → Prop} (C : LayerCellContract m front update P)
    {s : S} (hs : P s) (hf : FrontInvariant m front s) (j : ℤ) :
    front s j ≤ front (executeLayer m front update s) j :=
  (executeRows_spec C (layerRows m) (fun _ h => mem_layerRows.mp h) hs hf).2.2.1 j

end GapFamily.Construction
