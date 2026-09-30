import GapFamily.Layer

/-! Literal natural recursion for consecutive finite layer transitions. -/

namespace GapFamily.Construction

variable {S : Type*}

/-- Starting at layer `T`, perform each supplied layer transition exactly once,
in increasing order. The state sequence is constructed by natural recursion. -/
def layerIteration (T : ℕ) (layer : ℕ → S → S) (initial : S) : ℕ → S
  | 0 => initial
  | n + 1 => layer (T + n) (layerIteration T layer initial n)

@[simp] theorem layerIteration_zero (T : ℕ) (layer : ℕ → S → S) (initial : S) :
    layerIteration T layer initial 0 = initial := rfl

@[simp] theorem layerIteration_succ (T : ℕ) (layer : ℕ → S → S) (initial : S) (n : ℕ) :
    layerIteration T layer initial (n + 1) = layer (T + n) (layerIteration T layer initial n) := rfl

/-- Every finite prefix is the actual fold over its consecutive layer indices. -/
theorem layerIteration_eq_foldl (T : ℕ) (layer : ℕ → S → S) (initial : S) (n : ℕ) :
    layerIteration T layer initial n =
      (List.range n).foldl (fun s k => layer (T + k) s) initial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [layerIteration_succ, List.range_succ, List.foldl_append, ih]

/-- Restarting at any constructed stage gives exactly the same later states. -/
theorem layerIteration_add (T : ℕ) (layer : ℕ → S → S) (initial : S) (n k : ℕ) :
    layerIteration T layer initial (n + k) =
      layerIteration (T + n) layer (layerIteration T layer initial n) k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [Nat.add_succ, layerIteration_succ, ih, Nat.add_assoc]

/-- A stage-dependent predicate holds along the actual recursively constructed
sequence whenever each supplied transition preserves its next-stage predicate. -/
theorem layerIteration_invariant (T : ℕ) (layer : ℕ → S → S) (initial : S)
    (P : ℕ → S → Prop) (hinitial : P 0 initial)
    (hstep : ∀ n s, P n s → P (n + 1) (layer (T + n) s)) :
    ∀ n, P n (layerIteration T layer initial n) := by
  intro n
  induction n with
  | zero => exact hinitial
  | succ n ih => exact hstep n _ ih

/-- The same induction when the invariant is indexed by the absolute layer. -/
theorem layerIteration_absolute_invariant (T : ℕ) (layer : ℕ → S → S) (initial : S)
    (P : ℕ → S → Prop) (hinitial : P T initial)
    (hstep : ∀ m, T ≤ m → ∀ s, P m s → P (m + 1) (layer m s)) :
    ∀ n, P (T + n) (layerIteration T layer initial n) := by
  apply layerIteration_invariant T layer initial (fun n => P (T + n))
  · simpa using hinitial
  · intro n s hs
    simpa only [Nat.add_assoc] using hstep (T + n) (Nat.le_add_right _ _) s hs

/-- A supplied local layer proof propagates both the substantive state invariant
and the exact advancing-front bound at every constructed stage. -/
theorem layerIteration_state_front (T : ℕ) (layer : ℕ → S → S) (initial : S)
    (P : ℕ → S → Prop) (front : S → ℤ → ℝ)
    (hP : P 0 initial)
    (hfront : ∀ j : ℤ, max (T : ℝ) |(j : ℝ)| ≤ front initial j)
    (hstep : ∀ n s, P n s →
      (∀ j : ℤ, max ((T + n : ℕ) : ℝ) |(j : ℝ)| ≤ front s j) →
      P (n + 1) (layer (T + n) s) ∧
        ∀ j : ℤ, max ((T + n + 1 : ℕ) : ℝ) |(j : ℝ)| ≤ front (layer (T + n) s) j) :
    ∀ n, P n (layerIteration T layer initial n) ∧
      ∀ j : ℤ, max ((T + n : ℕ) : ℝ) |(j : ℝ)| ≤
        front (layerIteration T layer initial n) j := by
  apply layerIteration_invariant T layer initial
    (fun n s => P n s ∧ ∀ j : ℤ, max ((T + n : ℕ) : ℝ) |(j : ℝ)| ≤ front s j)
  · simpa using And.intro hP hfront
  · intro n s hs
    simpa only [Nat.add_assoc] using hstep n s hs.1 hs.2

/-- Every fixed finite energy cutoff is eventually behind each actual front
once the stage bounds have been established. -/
theorem layerIteration_front_eventually_above (T : ℕ) (layer : ℕ → S → S) (initial : S)
    (front : S → ℤ → ℝ)
    (hfront : ∀ n (j : ℤ), max ((T + n : ℕ) : ℝ) |(j : ℝ)| ≤
      front (layerIteration T layer initial n) j) (R : ℝ) :
    ∃ n : ℕ, ∀ k, n ≤ k → ∀ j : ℤ, R ≤ front (layerIteration T layer initial k) j := by
  obtain ⟨n, hn⟩ := exists_nat_ge R
  refine ⟨n, fun k hnk j => ?_⟩
  have hnk' : (n : ℝ) ≤ ((T + k : ℕ) : ℝ) :=
    Nat.cast_le.mpr (hnk.trans (Nat.le_add_left _ _))
  exact hn.trans (hnk'.trans ((le_max_left _ _).trans (hfront k j)))

/-- Once every layer has an explicit monotonicity proof, no later finite stage
can move any observed front backwards. -/
theorem layerIteration_monotone_front (T : ℕ) (layer : ℕ → S → S) (initial : S)
    (front : S → ℤ → ℝ)
    (hstep : ∀ m, T ≤ m → ∀ s j, front s j ≤ front (layer m s) j) (j : ℤ) :
    Monotone (fun n => front (layerIteration T layer initial n) j) := by
  apply monotone_nat_of_le_succ
  intro n
  exact hstep (T + n) (Nat.le_add_right _ _) _ j

end GapFamily.Construction
