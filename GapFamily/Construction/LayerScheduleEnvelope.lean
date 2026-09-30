import GapFamily.Construction.LayerScheduleRecurrence
import GapFamily.Construction.LayerScheduleError
import GapFamily.Construction.LayerScheduleConstruction

/-! The finite error estimate is imposed only on the still-unprocessed
continuum. Its domain shrinks by the proved frontier monotonicity. -/

noncomputable section
namespace GapFamily.Construction

variable {S A : Type*} [NormedAddCommGroup A]

/-- Energy-spin points at or above their current row frontier. -/
def Unprocessed (front : S → ℤ → ℝ) (s : S) (p : ℝ × ℤ) : Prop :=
  front s p.2 ≤ p.1

theorem executeLayer_unprocessed_subset {m : ℕ} {front : S → ℤ → ℝ}
    {update : ℤ → S → S} {P : S → Prop} (C : LayerCellContract m front update P)
    {s : S} (hs : P s) (hf : FrontInvariant m front s)
    {p : ℝ × ℤ} (hp : Unprocessed front (executeLayer m front update s) p) :
    Unprocessed front s p :=
  (executeLayer_front_mono C hs hf p.2).trans hp

/-- The exact layer allowance controls the actual guarded fold, from a bound
on each executed cell at points still unprocessed after that cell. -/
theorem executeLayer_error {m : ℕ} {front : S → ℤ → ℝ}
    {update : ℤ → S → S} {P : S → Prop} (C : LayerCellContract m front update P)
    (q : S → ℝ × ℤ → A) (H : ℝ × ℤ → ℝ) (hH : ∀ p, 0 ≤ H p)
    (herror : ∀ s j, P s → CanExecute m front s j → ∀ p,
      Unprocessed front (update j s) p →
        ‖q (update j s) p - q s p‖ ≤ Layer.slotBudget m * H p)
    {s : S} (hs : P s) (hf : FrontInvariant m front s)
    (p : ℝ × ℤ) (hp : Unprocessed front (executeLayer m front update s) p) :
    ‖q (executeLayer m front update s) p - q s p‖ ≤ Layer.layerBudget m * H p := by
  rw [executeLayer_eq_slot_fold] at hp ⊢
  apply norm_layerSlots_sub_le m (executeSlot m front update)
    (fun t => P t ∧ FrontInvariant m front t) (Unprocessed front) q H
    (fun j hj t ht => executeSlot_invariant C ht.1 ht.2 hj)
    (fun j hj t ht p hp => (executeSlot_front_mono C ht.1 ht.2 hj p.2).trans hp)
    ?_ s ⟨hs, hf⟩ p hp
  intro j hj t ht p hp
  by_cases hclear : (m : ℝ) + 1 ≤ front t j
  · rw [executeSlot_of_cleared _ _ _ _ _ hclear, sub_self, norm_zero]
    exact mul_nonneg (by unfold Layer.slotBudget; positivity) (hH p)
  · have hc : CanExecute m front t j :=
      ⟨hj, (le_max_left _ _).trans (ht.2 j), lt_of_not_ge hclear⟩
    rw [executeSlot_of_uncleared _ _ _ _ _ hc.2.2] at hp ⊢
    exact herror t j ht.1 hc p hp

/-- The old reference error and the current layer error add only on the
remaining continuum; cleared energies require no reference-envelope premise. -/
theorem executeLayer_error_reference {m : ℕ} {front : S → ℤ → ℝ}
    {update : ℤ → S → S} {P : S → Prop} (C : LayerCellContract m front update P)
    (q : S → ℝ × ℤ → A) (H : ℝ × ℤ → ℝ) (hH : ∀ p, 0 ≤ H p)
    (herror : ∀ s j, P s → CanExecute m front s j → ∀ p,
      Unprocessed front (update j s) p →
        ‖q (update j s) p - q s p‖ ≤ Layer.slotBudget m * H p)
    {s : S} (hs : P s) (hf : FrontInvariant m front s)
    (reference : ℝ × ℤ → A) (cost : ℝ)
    (hinitial : ∀ p, Unprocessed front s p → ‖q s p - reference p‖ ≤ cost * H p)
    (p : ℝ × ℤ) (hp : Unprocessed front (executeLayer m front update s) p) :
    ‖q (executeLayer m front update s) p - reference p‖ ≤
      (cost + Layer.layerBudget m) * H p := by
  calc
    _ ≤ ‖q (executeLayer m front update s) p - q s p‖ + ‖q s p - reference p‖ := by
      simpa only [dist_eq_norm] using
        dist_triangle (q (executeLayer m front update s) p) (q s p) (reference p)
    _ ≤ Layer.layerBudget m * H p + cost * H p :=
      add_le_add (executeLayer_error C q H hH herror hs hf p hp)
        (hinitial p (executeLayer_unprocessed_subset C hs hf hp))
    _ = _ := by ring

section Iteration

variable (T : ℕ) (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S)
  (initial : S) (P : S → Prop)
  (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
  (q : S → ℝ × ℤ → A) (H : ℝ × ℤ → ℝ) (hH : ∀ p, 0 ≤ H p)
  (herror : ∀ m, T ≤ m → ∀ s j, P s → CanExecute m front s j → ∀ p,
    Unprocessed front (update m j s) p →
      ‖q (update m j s) p - q s p‖ ≤ Layer.slotBudget m * H p)
  (hP : P initial) (hf : FrontInvariant T front initial)
  (reference : ℝ × ℤ → A)

include C hH herror hP hf

/-- Every finite actual prefix spends precisely the sum of its layer
allowances. No infinite state or pointwise bound on cleared rows is assumed. -/
theorem scheduledLayerState_error_reference (cost : ℝ)
    (hinitial : ∀ p, Unprocessed front initial p →
      ‖q initial p - reference p‖ ≤ cost * H p) :
    ∀ n p, Unprocessed front (scheduledLayerState T front update initial n) p →
      ‖q (scheduledLayerState T front update initial n) p - reference p‖ ≤
        (cost + ∑ r ∈ Finset.range n, Layer.layerBudget (T + r)) * H p := by
  intro n
  induction n with
  | zero => simpa using hinitial
  | succ n ih =>
    intro p hp
    have hm : T ≤ T + n := Nat.le_add_right _ _
    have hi := scheduledLayerState_invariant T front update initial P C hP hf n
    have hnext := executeLayer_error_reference (C (T + n) hm) q H hH (herror (T + n) hm)
      hi.1 hi.2 reference (cost + ∑ r ∈ Finset.range n, Layer.layerBudget (T + r)) ih p hp
    simpa only [scheduledLayerState_succ, Finset.sum_range_succ, add_assoc] using hnext

/-- The finite tail allowance is uniformly at most `1/256`, independently of
the number of completed layers and of the final unprocessed point. -/
theorem scheduledLayerState_error_budget (cost : ℝ)
    (hinitial : ∀ p, Unprocessed front initial p →
      ‖q initial p - reference p‖ ≤ cost * H p)
    (n : ℕ) (p : ℝ × ℤ)
    (hp : Unprocessed front (scheduledLayerState T front update initial n) p) :
    ‖q (scheduledLayerState T front update initial n) p - reference p‖ ≤
      (cost + 1 / 256) * H p := by
  have hsum : (∑ r ∈ Finset.range n, Layer.layerBudget (T + r)) ≤ (1 / 256 : ℝ) := by
    rw [sum_layerBudget_add]
    have hleft : (1 : ℝ) / ((T : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) T]
    have hright : 0 ≤ (1 : ℝ) / ((T : ℝ) + (n : ℝ) + 1) := by positivity
    nlinarith
  exact (scheduledLayerState_error_reference T front update initial P C q H hH herror
    hP hf reference cost hinitial n p hp).trans
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl hsum) (hH p))

/-- Reference error `H/2`, initial-cell error `H/8`, and every scheduled tail
correction together stay at `161 H / 256`, strictly below `H` when `H > 0`. -/
theorem scheduledLayerState_error_closes
    (hinitial : ∀ p, Unprocessed front initial p →
      ‖q initial p - reference p‖ ≤ (1 / 2 + 1 / 8 : ℝ) * H p)
    (n : ℕ) (p : ℝ × ℤ)
    (hp : Unprocessed front (scheduledLayerState T front update initial n) p) :
    ‖q (scheduledLayerState T front update initial n) p - reference p‖ ≤
        (161 / 256 : ℝ) * H p ∧
      (0 < H p → ‖q (scheduledLayerState T front update initial n) p - reference p‖ < H p) := by
  have hbound := scheduledLayerState_error_budget T front update initial P C q H hH herror
    hP hf reference (1 / 2 + 1 / 8) hinitial n p hp
  norm_num at hbound
  exact ⟨hbound, fun hp => by nlinarith⟩

end Iteration

end GapFamily.Construction
