import GapFamily.Construction.InitialFront
import GapFamily.Construction.LayerScheduleIteration
import GapFamily.Construction.LayerScheduleRecurrence
import GapFamily.Construction.LayerScheduleFlatIteration

/-! The actual C9 sequence, built by iterating the prescribed finite slot fold.
Only one-cell contracts are hypotheses; layer and stage invariants are proved. -/

noncomputable section
namespace GapFamily.Construction

variable {S : Type*}

/-- The actual state after `n` layers starting at `T`. Each layer is the fixed
ordered two-slot schedule, with the supplied cell update used only when needed. -/
def scheduledLayerState (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) : ℕ → S :=
  layerIteration T (fun m => executeLayer m front (update m)) initial

@[simp] theorem scheduledLayerState_zero (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) :
    scheduledLayerState T front update initial 0 = initial := rfl

@[simp] theorem scheduledLayerState_succ (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (n : ℕ) :
    scheduledLayerState T front update initial (n + 1) =
      executeLayer (T + n) front (update (T + n))
        (scheduledLayerState T front update initial n) := rfl

/-- The next actual state is the literal fold of the fixed finite slot list. -/
theorem scheduledLayerState_succ_eq_slot_fold (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (n : ℕ) :
    scheduledLayerState T front update initial (n + 1) =
      (layerSlots (T + n)).foldl
        (fun state j => executeSlot (T + n) front (update (T + n)) j state)
        (scheduledLayerState T front update initial n) :=
  executeLayer_eq_slot_fold _ _ _ _

/-- Flattening all completed layers gives exactly the same state and the
literal finite prefix of `2 * n * (2 * T + n)` guarded slots. -/
theorem scheduledLayerState_eq_slotPrefix_fold (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (n : ℕ) :
    scheduledLayerState T front update initial n =
      (scheduledSlotPrefix T n).foldl
        (fun state p => executeSlot p.1 front (update p.1) p.2 state) initial :=
  layerIteration_eq_scheduledSlotPrefix_fold T front update initial n

theorem scheduledLayerState_add (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (n k : ℕ) :
    scheduledLayerState T front update initial (n + k) =
      scheduledLayerState (T + n) front update
        (scheduledLayerState T front update initial n) k :=
  layerIteration_add T (fun m => executeLayer m front (update m)) initial n k

/-- Stage-dependent state assertions and all row fronts persist along the actual
schedule. The rollover premise only reindexes an already established state
assertion once the next frontier is reached. -/
theorem scheduledLayerState_indexed_invariant (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (P : ℕ → S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) (P m))
    (hroll : ∀ m, T ≤ m → ∀ s, P m s → FrontInvariant (m + 1) front s → P (m + 1) s)
    (hP : P T initial) (hf : FrontInvariant T front initial) :
    ∀ n, P (T + n) (scheduledLayerState T front update initial n) ∧
      FrontInvariant (T + n) front (scheduledLayerState T front update initial n) := by
  intro n
  induction n with
  | zero => simpa using And.intro hP hf
  | succ n ih =>
    have hm : T ≤ T + n := Nat.le_add_right _ _
    have hnext := executeLayer_invariant (C (T + n) hm) ih.1 ih.2
    have hPnext := hroll (T + n) hm _ hnext.1 hnext.2
    simpa only [scheduledLayerState_succ, Nat.add_assoc] using And.intro hPnext hnext.2

/-- A uniform state invariant needs only the local cell contracts, with no
assumed complete-layer transition or recursively chosen state sequence. -/
theorem scheduledLayerState_invariant (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (P : S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
    (hP : P initial) (hf : FrontInvariant T front initial) :
    ∀ n, P (scheduledLayerState T front update initial n) ∧
      FrontInvariant (T + n) front (scheduledLayerState T front update initial n) :=
  scheduledLayerState_indexed_invariant T front update initial (fun _ => P) C
    (fun _ _ _ hs _ => hs) hP hf

/-- Local cell monotonicity makes every actual row front monotone in the stage. -/
theorem scheduledLayerState_indexed_front_monotone (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (P : ℕ → S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) (P m))
    (hroll : ∀ m, T ≤ m → ∀ s, P m s → FrontInvariant (m + 1) front s → P (m + 1) s)
    (hP : P T initial) (hf : FrontInvariant T front initial) (j : ℤ) :
    Monotone (fun n => front (scheduledLayerState T front update initial n) j) := by
  apply monotone_nat_of_le_succ
  intro n
  have hi := scheduledLayerState_indexed_invariant T front update initial P C hroll hP hf n
  exact executeLayer_front_mono (C (T + n) (Nat.le_add_right _ _)) hi.1 hi.2 j

theorem scheduledLayerState_front_monotone (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (P : S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
    (hP : P initial) (hf : FrontInvariant T front initial) (j : ℤ) :
    Monotone (fun n => front (scheduledLayerState T front update initial n) j) :=
  scheduledLayerState_indexed_front_monotone T front update initial (fun _ => P) C
    (fun _ _ _ hs _ => hs) hP hf j

/-- Every fixed energy cutoff is eventually behind every front of the actual
scheduled construction, uniformly in the integer spin. -/
theorem scheduledLayerState_eventually_above (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (P : S → Prop)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
    (hP : P initial) (hf : FrontInvariant T front initial) (R : ℝ) :
    ∃ n : ℕ, ∀ k, n ≤ k → ∀ j : ℤ,
      R ≤ front (scheduledLayerState T front update initial k) j := by
  apply layerIteration_front_eventually_above T
    (fun m => executeLayer m front (update m)) initial front _ R
  intro n j
  exact (scheduledLayerState_invariant T front update initial P C hP hf n).2 j

/-- The concrete initial-front formula establishes the required start condition. -/
theorem frontInvariant_of_initialFront (T : ℕ) (front : S → ℤ → ℝ)
    (initial : S) (endpoint : ℤ → ℝ)
    (hfront : ∀ j, front initial j = initialFront (T : ℝ) endpoint j)
    (hT : ∀ j : ℤ, |(j : ℝ)| ≤ (T : ℝ) → (T : ℝ) ≤ endpoint j)
    (hspin : ∀ j : ℤ, |(j : ℝ)| ≤ (T : ℝ) → |(j : ℝ)| ≤ endpoint j) :
    FrontInvariant T front initial := by
  intro j
  rw [hfront j]
  exact max_le_initialFront (T : ℝ) endpoint hT hspin j

/-- Explicit initial endpoints and one-cell contracts yield every stage of the
literal finite-slot recursion together with its substantive and front invariants. -/
theorem scheduledLayerState_of_initialFront (T : ℕ) (front : S → ℤ → ℝ)
    (update : ℕ → ℤ → S → S) (initial : S) (P : S → Prop)
    (endpoint : ℤ → ℝ)
    (hfront : ∀ j, front initial j = initialFront (T : ℝ) endpoint j)
    (hT : ∀ j : ℤ, |(j : ℝ)| ≤ (T : ℝ) → (T : ℝ) ≤ endpoint j)
    (hspin : ∀ j : ℤ, |(j : ℝ)| ≤ (T : ℝ) → |(j : ℝ)| ≤ endpoint j)
    (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P) (hP : P initial) :
    ∀ n, P (scheduledLayerState T front update initial n) ∧
      FrontInvariant (T + n) front (scheduledLayerState T front update initial n) :=
  scheduledLayerState_invariant T front update initial P C hP
    (frontInvariant_of_initialFront T front initial endpoint hfront hT hspin)

end GapFamily.Construction
