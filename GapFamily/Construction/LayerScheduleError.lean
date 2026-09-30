import GapFamily.Construction.LayerSchedule

/-! Accumulation of local errors along the literal finite layer schedule. -/

namespace GapFamily.Construction

section Finite

variable {I S X A : Type*} [NormedAddCommGroup A]

/-- Local error contracts accumulate at every point which is still active after
the fold. The invariant and backward inclusion of active sets are proved together. -/
theorem foldl_active_error (slots : List I) (step : I → S → S)
    (P : S → Prop) (active : S → X → Prop) (q : S → X → A)
    (cost : I → ℝ) (H : X → ℝ)
    (hvalid : ∀ i ∈ slots, ∀ s, P s → P (step i s))
    (hactive : ∀ i ∈ slots, ∀ s, P s → ∀ x, active (step i s) x → active s x)
    (herror : ∀ i ∈ slots, ∀ s, P s → ∀ x, active (step i s) x →
      ‖q (step i s) x - q s x‖ ≤ cost i * H x)
    (s : S) (hs : P s) :
    P (slots.foldl (fun state i => step i state) s) ∧
      ∀ x, active (slots.foldl (fun state i => step i state) s) x →
        active s x ∧
          ‖q (slots.foldl (fun state i => step i state) s) x - q s x‖ ≤
            (slots.map cost).sum * H x := by
  induction slots generalizing s with
  | nil =>
      exact ⟨hs, fun x hx => ⟨hx, by simp⟩⟩
  | cons i slots ih =>
      have hi : i ∈ i :: slots := List.mem_cons_self
      obtain ⟨hfinal, htail⟩ := ih
        (fun j hj => hvalid j (List.mem_cons_of_mem _ hj))
        (fun j hj => hactive j (List.mem_cons_of_mem _ hj))
        (fun j hj => herror j (List.mem_cons_of_mem _ hj))
        (step i s) (hvalid i hi s hs)
      refine ⟨hfinal, ?_⟩
      intro x hx
      obtain ⟨hxnext, hbound⟩ := htail x hx
      refine ⟨hactive i hi s hs x hxnext, ?_⟩
      calc
        ‖q ((i :: slots).foldl (fun state j => step j state) s) x - q s x‖ ≤
            ‖q (slots.foldl (fun state j => step j state) (step i s)) x -
              q (step i s) x‖ + ‖q (step i s) x - q s x‖ := by
          simpa only [dist_eq_norm, List.foldl_cons] using dist_triangle
            (q (slots.foldl (fun state j => step j state) (step i s)) x)
            (q (step i s) x) (q s x)
        _ ≤ (slots.map cost).sum * H x + cost i * H x :=
          add_le_add hbound (herror i hi s hs x hxnext)
        _ = ((i :: slots).map cost).sum * H x := by simp [add_mul, add_comm]

/-- The accumulated correction bound follows from contracts on the visited slots. -/
theorem norm_foldl_sub_le (slots : List I) (step : I → S → S)
    (P : S → Prop) (active : S → X → Prop) (q : S → X → A)
    (cost : I → ℝ) (H : X → ℝ)
    (hvalid : ∀ i ∈ slots, ∀ s, P s → P (step i s))
    (hactive : ∀ i ∈ slots, ∀ s, P s → ∀ x, active (step i s) x → active s x)
    (herror : ∀ i ∈ slots, ∀ s, P s → ∀ x, active (step i s) x →
      ‖q (step i s) x - q s x‖ ≤ cost i * H x)
    (s : S) (hs : P s) (x : X)
    (hx : active (slots.foldl (fun state i => step i state) s) x) :
    ‖q (slots.foldl (fun state i => step i state) s) x - q s x‖ ≤
      (slots.map cost).sum * H x :=
  ((foldl_active_error slots step P active q cost H hvalid hactive herror s hs).2 x hx).2

/-- An initial error relative to a fixed reference adds to the total slot cost. -/
theorem norm_foldl_sub_reference_le (slots : List I) (step : I → S → S)
    (P : S → Prop) (active : S → X → Prop) (q : S → X → A)
    (cost : I → ℝ) (H : X → ℝ)
    (hvalid : ∀ i ∈ slots, ∀ s, P s → P (step i s))
    (hactive : ∀ i ∈ slots, ∀ s, P s → ∀ x, active (step i s) x → active s x)
    (herror : ∀ i ∈ slots, ∀ s, P s → ∀ x, active (step i s) x →
      ‖q (step i s) x - q s x‖ ≤ cost i * H x)
    (s : S) (hs : P s) (reference : X → A) (initialCost : ℝ)
    (hinitial : ∀ x, active s x → ‖q s x - reference x‖ ≤ initialCost * H x)
    (x : X) (hx : active (slots.foldl (fun state i => step i state) s) x) :
    ‖q (slots.foldl (fun state i => step i state) s) x - reference x‖ ≤
      (initialCost + (slots.map cost).sum) * H x := by
  obtain ⟨hxinitial, hbound⟩ :=
    (foldl_active_error slots step P active q cost H hvalid hactive herror s hs).2 x hx
  calc
    _ ≤ ‖q (slots.foldl (fun state i => step i state) s) x - q s x‖ +
        ‖q s x - reference x‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (q (slots.foldl (fun state i => step i state) s) x) (q s x) (reference x)
    _ ≤ (slots.map cost).sum * H x + initialCost * H x :=
      add_le_add hbound (hinitial x hxinitial)
    _ = (initialCost + (slots.map cost).sum) * H x := by ring

end Finite

section Layer

variable {S X A : Type*} [NormedAddCommGroup A]

/-- On the actual two-slot-per-row schedule, the uniform slot allowance sums to
the existing layer budget. Physical validity of the contracts remains a hypothesis. -/
theorem norm_layerSlots_sub_le (m : ℕ) (step : ℤ → S → S)
    (P : S → Prop) (active : S → X → Prop) (q : S → X → A) (H : X → ℝ)
    (hvalid : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ s, P s → P (step j s))
    (hactive : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ s, P s →
      ∀ x, active (step j s) x → active s x)
    (herror : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ s, P s →
      ∀ x, active (step j s) x → ‖q (step j s) x - q s x‖ ≤ Layer.slotBudget m * H x)
    (s : S) (hs : P s) (x : X)
    (hx : active ((layerSlots m).foldl (fun state j => step j state) s) x) :
    ‖q ((layerSlots m).foldl (fun state j => step j state) s) x - q s x‖ ≤
      Layer.layerBudget m * H x := by
  simpa only [sum_layerSlots_slotBudget] using
    norm_foldl_sub_le (layerSlots m) step P active q (fun _ => Layer.slotBudget m) H
      (fun j hj => hvalid j ((mem_layerSlots m j).mp hj))
      (fun j hj => hactive j ((mem_layerSlots m j).mp hj))
      (fun j hj => herror j ((mem_layerSlots m j).mp hj)) s hs x hx

/-- The layer budget controls the growth of error relative to the same reference. -/
theorem norm_layerSlots_sub_reference_le (m : ℕ) (step : ℤ → S → S)
    (P : S → Prop) (active : S → X → Prop) (q : S → X → A) (H : X → ℝ)
    (hvalid : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ s, P s → P (step j s))
    (hactive : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ s, P s →
      ∀ x, active (step j s) x → active s x)
    (herror : ∀ j : ℤ, |j| ≤ (m : ℤ) → ∀ s, P s →
      ∀ x, active (step j s) x → ‖q (step j s) x - q s x‖ ≤ Layer.slotBudget m * H x)
    (s : S) (hs : P s) (reference : X → A) (initialCost : ℝ)
    (hinitial : ∀ x, active s x → ‖q s x - reference x‖ ≤ initialCost * H x)
    (x : X) (hx : active ((layerSlots m).foldl (fun state j => step j state) s) x) :
    ‖q ((layerSlots m).foldl (fun state j => step j state) s) x - reference x‖ ≤
      (initialCost + Layer.layerBudget m) * H x := by
  simpa only [sum_layerSlots_slotBudget] using
    norm_foldl_sub_reference_le (layerSlots m) step P active q
      (fun _ => Layer.slotBudget m) H
      (fun j hj => hvalid j ((mem_layerSlots m j).mp hj))
      (fun j hj => hactive j ((mem_layerSlots m j).mp hj))
      (fun j hj => herror j ((mem_layerSlots m j).mp hj))
      s hs reference initialCost hinitial x hx

end Layer

end GapFamily.Construction
