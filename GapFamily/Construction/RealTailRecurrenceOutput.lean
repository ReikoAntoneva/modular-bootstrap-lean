import GapFamily.Construction.RealTailRecurrence
import GapFamily.Construction.LayerScheduleConstruction

/-! Geometric clearance and generic output preservation for the real-parameter
recursion. The generic predicate supports arbitrary reference seeds and markers. -/

noncomputable section
namespace GapFamily.Construction
open Set Real Analytic
namespace RealTailLocalData
variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
variable (d : RealTailLocalData a U T degree)

/-- Every actual update preserves the upper front bound within its layer. -/
theorem step_layer_front_upper (m : ℕ) (J : ℤ) (st : FiniteRepairState)
    (hf : ∀ j : ℤ, st.front j ≤ max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|)) :
    ∀ j : ℤ, (d.step m J st).front j ≤ max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|) := by
  by_cases h : RealTailStepValid a T st m J
  · rw [d.step_valid h]
    exact st.addTailCell_layer_front_upper _ _ _ _ _ hf h.front_upper
  · rwa [d.step_invalid h]

/-- The actual repair cutoff contains the cleared physical region. -/
theorem step_cleared (m : ℕ) (J : ℤ) (st : FiniteRepairState) (hc : st.Cleared)
    (hf : ∀ j : ℤ, st.front j ≤ max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|)) :
    (d.step m J st).Cleared := by
  by_cases h : RealTailStepValid a T st m J
  · rw [d.step_valid h]
    exact st.addTailCell_cleared _ _ _ _ _ hc
      (st.front_le_layerCutoff_of_layer_upper d.cutoff_nonneg hf)
  · rwa [d.step_invalid h]

/-- Any output identity preserved by one actual cell persists through the
whole recursion, independently of the reference seed used to initialize it. -/
theorem step_preserves (P : FiniteRepairState → Prop)
    (hP : ∀ (st : FiniteRepairState) (m : ℕ) (J : ℤ)
      (h : RealTailStepValid a T st m J), P st →
      P (st.addTailCell (d.cell st m J h) (layerCutoff U m)
        (one_le_layerCutoff d.cutoff_nonneg m) h.physical
        ((d.cell st m J h).right_lt_layerCutoff d.cutoff_nonneg h.front_upper)))
    (m : ℕ) (J : ℤ) (st : FiniteRepairState) (hPst : P st) : P (d.step m J st) := by
  by_cases h : RealTailStepValid a T st m J
  · rw [d.step_valid h]
    exact hP st m J h hPst
  · rwa [d.step_invalid h]

theorem slot_fold_invariant (P : FiniteRepairState → Prop)
    (hP : ∀ (st : FiniteRepairState) (m : ℕ) (J : ℤ)
      (h : RealTailStepValid a T st m J), P st →
      P (st.addTailCell (d.cell st m J h) (layerCutoff U m)
        (one_le_layerCutoff d.cutoff_nonneg m) h.physical
        ((d.cell st m J h).right_lt_layerCutoff d.cutoff_nonneg h.front_upper)))
    (m : ℕ) (slots : List ℤ) (st : FiniteRepairState) (ho : P st)
    (hi : st.ThermalIntegrable) (hc : st.Cleared)
    (hf : ∀ j : ℤ, st.front j ≤ max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|)) :
    let next := slots.foldl
      (fun st J => executeSlot m FiniteRepairState.front (d.step m) J st) st
    P next ∧ next.ThermalIntegrable ∧ next.Cleared ∧
      ∀ j : ℤ, next.front j ≤ max (U + 1) (max ((m : ℝ) + 2) |(j : ℝ)|) := by
  induction slots generalizing st with
  | nil => exact ⟨ho, hi, hc, hf⟩
  | cons J slots ih =>
    simp only [List.foldl_cons]
    by_cases hclear : (m : ℝ) + 1 ≤ st.front J
    · rw [executeSlot_of_cleared _ _ _ _ _ hclear]
      exact ih st ho hi hc hf
    · rw [executeSlot_of_uncleared _ _ _ _ _ (lt_of_not_ge hclear)]
      exact ih _ (d.step_preserves P hP m J st ho) (d.step_thermalIntegrable m J st hi)
        (d.step_cleared m J st hc hf) (d.step_layer_front_upper m J st hf)

theorem state_output_invariant (P : FiniteRepairState → Prop)
    (hP : ∀ (st : FiniteRepairState) (m : ℕ) (J : ℤ)
      (h : RealTailStepValid a T st m J), P st →
      P (st.addTailCell (d.cell st m J h) (layerCutoff U m)
        (one_le_layerCutoff d.cutoff_nonneg m) h.physical
        ((d.cell st m J h).right_lt_layerCutoff d.cutoff_nonneg h.front_upper)))
    (initial : FiniteRepairState) (ho : P initial) (hi : initial.ThermalIntegrable)
    (hc : initial.Cleared)
    (hf : ∀ j : ℤ, initial.front j ≤ max (U + 1) (max ((T : ℝ) + 1) |(j : ℝ)|))
    (k : ℕ) :
    P (d.state initial k) ∧ (d.state initial k).ThermalIntegrable ∧
      (d.state initial k).Cleared ∧ ∀ j : ℤ, (d.state initial k).front j ≤
        max (U + 1) (max (((T + k : ℕ) : ℝ) + 1) |(j : ℝ)|) := by
  induction k with
  | zero => simpa only [state_zero, Nat.add_zero] using
      And.intro ho (And.intro hi (And.intro hc hf))
  | succ k ih =>
    obtain ⟨hok, hik, hck, hfk⟩ := ih
    obtain ⟨hon, hin, hcn, hfn⟩ := d.slot_fold_invariant P hP (T + k)
      (layerSlots (T + k)) _ hok hik hck (FiniteRepairState.layer_start_front_upper _ hfk)
    unfold state
    rw [scheduledLayerState_succ_eq_slot_fold]
    refine ⟨hon, hin, hcn, ?_⟩
    simpa only [Nat.add_assoc, state] using FiniteRepairState.layer_front_upper_succ _ hfn

theorem partialState_output_invariant (P : FiniteRepairState → Prop)
    (hP : ∀ (st : FiniteRepairState) (m : ℕ) (J : ℤ)
      (h : RealTailStepValid a T st m J), P st →
      P (st.addTailCell (d.cell st m J h) (layerCutoff U m)
        (one_le_layerCutoff d.cutoff_nonneg m) h.physical
        ((d.cell st m J h).right_lt_layerCutoff d.cutoff_nonneg h.front_upper)))
    (initial : FiniteRepairState) (ho : P initial) (hi : initial.ThermalIntegrable)
    (hc : initial.Cleared)
    (hf : ∀ j : ℤ, initial.front j ≤ max (U + 1) (max ((T : ℝ) + 1) |(j : ℝ)|))
    (k r : ℕ) :
    P (d.partialState initial k r) ∧ (d.partialState initial k r).ThermalIntegrable ∧
      (d.partialState initial k r).Cleared ∧ ∀ j : ℤ, (d.partialState initial k r).front j ≤
        max (U + 1) (max (((T + k : ℕ) : ℝ) + 2) |(j : ℝ)|) := by
  obtain ⟨hok, hik, hck, hfk⟩ := d.state_output_invariant P hP initial ho hi hc hf k
  exact d.slot_fold_invariant P hP (T + k) ((layerSlots (T + k)).take r) _ hok hik hck
    (FiniteRepairState.layer_start_front_upper _ hfk)

/-- Node conditions such as physicality and strict separation from the marker
are retained by the actual finite node append operations. -/
theorem step_node_property (P : ℝ × ℤ → Prop)
    (m : ℕ) (J : ℤ) (st : FiniteRepairState)
    (hold : ∀ p ∈ st.nodes, P p) (hnew : ∀ p ∈ d.nodeList m J st, P p) :
    ∀ p ∈ (d.step m J st).nodes, P p := by
  rw [d.step_nodes]
  intro p hp
  exact (List.mem_append.mp hp).elim (hold p) (hnew p)

end RealTailLocalData
end GapFamily.Construction
