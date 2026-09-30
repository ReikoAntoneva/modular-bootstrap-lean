import GapFamily.Construction.TailCellStateGeometry
import GapFamily.Construction.FiniteRepairStateLocalIntegrability
import GapFamily.Construction.LayerSchedulePrefixBudget
import GapFamily.Construction.LayerScheduleError
import GapFamily.Construction.LayerScheduleReachability

/-! Actual finite tail recursion with real charge and cutoff. Its input consists
only of local cell existence and the exterior error estimate. -/

noncomputable section
namespace GapFamily.Construction
open Set Real Analytic
open scoped Classical

/-- Local hypotheses at a still active row of an absolute layer. -/
structure RealTailStepValid (a : ℝ) (T : ℕ) (state : FiniteRepairState)
    (m : ℕ) (J : ℤ) : Prop where
  layer : T ≤ m
  front_lower : (m : ℝ) ≤ state.front J
  front_upper : state.front J < (m : ℝ) + 1
  physical : |(J : ℝ)| ≤ state.front J
  thermal : state.ThermalIntegrable
  envelope : ∀ E ∈ Icc (state.front J) (state.front J + 1),
    |state.numerator J E - vacuumLeading a E J| ≤ exp (7 * sqrt (a * E))

/-- A purely local contract; no infinite spectrum is an input. -/
structure RealTailLocalData (a U : ℝ) (T : ℕ) (degree : ℕ → ℕ) where
  cutoff_nonneg : 0 ≤ U
  cell : ∀ (state : FiniteRepairState) (m : ℕ) (J : ℤ),
    RealTailStepValid a T state m J →
      TailCell J (state.front J) (degree m) (state.numerator J)
  error : ∀ (state : FiniteRepairState) (m : ℕ) (J : ℤ)
    (h : RealTailStepValid a T state m J) (j : ℤ) (E : ℝ),
    |(j : ℝ)| ≤ E → layerCutoff U m < E →
    |(cell state m J h).exteriorNumerator (layerCutoff U m)
        (one_le_layerCutoff cutoff_nonneg m) j E| ≤
      Layer.slotBudget m * exp (7 * sqrt (a * E))

namespace RealTailLocalData
variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
variable (d : RealTailLocalData a U T degree)

/-- A literal cell repair, with identity fallback outside its local hypotheses. -/
def step (m : ℕ) (J : ℤ) (state : FiniteRepairState) : FiniteRepairState :=
  if h : RealTailStepValid a T state m J then
    state.addTailCell (d.cell state m J h) (layerCutoff U m)
      (one_le_layerCutoff d.cutoff_nonneg m) h.physical
      ((d.cell state m J h).right_lt_layerCutoff d.cutoff_nonneg h.front_upper)
  else state

/-- The same selected cells supply the unit node occurrences. -/
def nodeList (m : ℕ) (J : ℤ) (state : FiniteRepairState) : List (ℝ × ℤ) :=
  if h : RealTailStepValid a T state m J then
    List.ofFn (fun i => ((d.cell state m J h).node i, J))
  else []

theorem step_valid {m : ℕ} {J : ℤ} {state : FiniteRepairState}
    (h : RealTailStepValid a T state m J) :
    d.step m J state = state.addTailCell (d.cell state m J h) (layerCutoff U m)
      (one_le_layerCutoff d.cutoff_nonneg m) h.physical
      ((d.cell state m J h).right_lt_layerCutoff d.cutoff_nonneg h.front_upper) := by
  simp only [step, dite_eq_left h]

theorem step_invalid {m : ℕ} {J : ℤ} {state : FiniteRepairState}
    (h : ¬RealTailStepValid a T state m J) : d.step m J state = state := by
  simp only [step, dite_eq_right h]

theorem step_front_mono (m : ℕ) (J : ℤ) (state : FiniteRepairState) (j : ℤ) :
    state.front j ≤ (d.step m J state).front j := by
  by_cases h : RealTailStepValid a T state m J
  · rw [d.step_valid h]
    exact state.addTailCell_front_mono _ _ _ _ _ j
  · rw [d.step_invalid h]

theorem step_front_same {m : ℕ} {J : ℤ} {state : FiniteRepairState}
    (h : RealTailStepValid a T state m J) :
    (d.step m J state).front J = (d.cell state m J h).right := by
  rw [d.step_valid h, FiniteRepairState.addTailCell_front_same]

theorem step_front_advance {m : ℕ} {J : ℤ} {state : FiniteRepairState}
    (h : RealTailStepValid a T state m J) :
    state.front J + 1 / 2 ≤ (d.step m J state).front J := by
  rw [d.step_front_same h]
  exact (d.cell state m J h).right_mem.1

theorem step_front_upper (m : ℕ) (J : ℤ) (state : FiniteRepairState) :
    (d.step m J state).front J ≤ state.front J + 1 := by
  by_cases h : RealTailStepValid a T state m J
  · rw [d.step_front_same h]
    exact (d.cell state m J h).right_mem.2
  · rw [d.step_invalid h]
    linarith

theorem step_front_other (m : ℕ) (J : ℤ) (state : FiniteRepairState)
    {j : ℤ} (hj : j ≠ J) : (d.step m J state).front j = state.front j := by
  by_cases h : RealTailStepValid a T state m J
  · rw [d.step_valid h]
    exact state.addTailCell_front_other _ _ _ _ _ hj
  · rw [d.step_invalid h]

theorem step_nodes (m : ℕ) (J : ℤ) (state : FiniteRepairState) :
    (d.step m J state).nodes = state.nodes ++ d.nodeList m J state := by
  by_cases h : RealTailStepValid a T state m J
  · rw [d.step_valid h]
    simp only [nodeList, dite_eq_left h]
    rfl
  · rw [d.step_invalid h]
    simp only [nodeList, dite_eq_right h, List.append_nil]

theorem nodeList_bounds (m : ℕ) (J : ℤ) (state : FiniteRepairState)
    (p : ℝ × ℤ) (hp : p ∈ d.nodeList m J state) :
    state.front J ≤ p.1 ∧ p.1 ≤ (d.step m J state).front J ∧ p.2 = J := by
  by_cases h : RealTailStepValid a T state m J
  · simp only [nodeList, dite_eq_left h] at hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    rw [d.step_front_same h]
    exact ⟨((d.cell state m J h).node_mem i).1,
      ((d.cell state m J h).node_mem i).2, rfl⟩
  · simp only [nodeList, dite_eq_right h, List.not_mem_nil] at hp

theorem nodeList_layer_bounds (m : ℕ) (J : ℤ) (state : FiniteRepairState)
    (p : ℝ × ℤ) (hp : p ∈ d.nodeList m J state) :
    (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2 ∧ |(p.2 : ℝ)| ≤ p.1 := by
  by_cases h : RealTailStepValid a T state m J
  · have hb := d.nodeList_bounds m J state p hp
    refine ⟨h.front_lower.trans hb.1, ?_, ?_⟩
    · exact (hb.2.1.trans (d.step_front_upper m J state)).trans_lt (by linarith [h.front_upper])
    · rw [hb.2.2]
      exact h.physical.trans hb.1
  · simp only [nodeList, dite_eq_right h, List.not_mem_nil] at hp

theorem step_thermalIntegrable (m : ℕ) (J : ℤ) (state : FiniteRepairState)
    (hi : state.ThermalIntegrable) : (d.step m J state).ThermalIntegrable := by
  by_cases h : RealTailStepValid a T state m J
  · rw [d.step_valid h]
    exact state.addTailCell_thermalIntegrable _ _ _ _ _ hi
  · rwa [d.step_invalid h]

/-- The identity branch makes the error estimate unconditional. -/
theorem step_error (m : ℕ) (J : ℤ) (state : FiniteRepairState)
    (j : ℤ) (E : ℝ) (hphysical : |(j : ℝ)| ≤ E)
    (hE : (d.step m J state).front j ≤ E) :
    |(d.step m J state).numerator j E - state.numerator j E| ≤
      Layer.slotBudget m * exp (7 * sqrt (a * E)) := by
  have hε : 0 ≤ Layer.slotBudget m := by unfold Layer.slotBudget; positivity
  by_cases h : RealTailStepValid a T state m J
  · rw [d.step_valid h] at hE ⊢
    exact state.addTailCell_error _ _ _ _ _ (Layer.slotBudget m)
      (fun e => exp (7 * sqrt (a * e))) hε (fun _ => (exp_pos _).le)
      (d.error state m J h) j E hphysical hE
  · rw [d.step_invalid h]
    simp only [sub_self, abs_zero]
    exact mul_nonneg hε (exp_pos _).le

/-- State after complete layers starting at the arbitrary integer `T`. -/
def state (initial : FiniteRepairState) (k : ℕ) : FiniteRepairState :=
  scheduledLayerState T FiniteRepairState.front d.step initial k

/-- State after a literal partial prefix of the next layer. -/
def partialState (initial : FiniteRepairState) (k r : ℕ) : FiniteRepairState :=
  ((layerSlots (T + k)).take r).foldl
    (fun state J => executeSlot (T + k) FiniteRepairState.front (d.step (T + k)) J state)
    (d.state initial k)

@[simp] theorem state_zero (initial : FiniteRepairState) : d.state initial 0 = initial := rfl
@[simp] theorem partialState_zero (initial : FiniteRepairState) (k : ℕ) :
    d.partialState initial k 0 = d.state initial k := by simp [partialState]

theorem state_succ (initial : FiniteRepairState) (k : ℕ) :
    d.state initial (k + 1) = executeLayer (T + k) FiniteRepairState.front
      (d.step (T + k)) (d.state initial k) := rfl

theorem partialState_eq_fold (initial : FiniteRepairState) (k r : ℕ) :
    d.partialState initial k r = (scheduledPartialSlotPrefix T k r).foldl
      (fun state p => executeSlot p.1 FiniteRepairState.front (d.step p.1) p.2 state) initial :=
  (scheduledPartialSlotPrefix_fold _ _ _ _ _ _).symm

theorem state_front_monotone (initial : FiniteRepairState) (j : ℤ) :
    Monotone (fun k => (d.state initial k).front j) :=
  scheduledLayerState_front_monotone_of_update _ _ _ initial d.step_front_mono j

theorem executeSlot_thermalIntegrable (m : ℕ) (J : ℤ) (state : FiniteRepairState)
    (hi : state.ThermalIntegrable) :
    (executeSlot m FiniteRepairState.front (d.step m) J state).ThermalIntegrable := by
  unfold executeSlot
  split_ifs
  · exact hi
  · exact d.step_thermalIntegrable m J state hi

/-- Every literal partial prefix retains ordinary thermal integrability. -/
theorem partialState_thermalIntegrable (initial : FiniteRepairState)
    (hi : initial.ThermalIntegrable) (k r : ℕ) :
    (d.partialState initial k r).ThermalIntegrable := by
  rw [d.partialState_eq_fold]
  have hfold (slots : List (ℕ × ℤ)) (st : FiniteRepairState)
      (hstate : st.ThermalIntegrable) :
      (slots.foldl (fun st p => executeSlot p.1 FiniteRepairState.front
        (d.step p.1) p.2 st) st).ThermalIntegrable := by
    induction slots generalizing st with
    | nil => exact hstate
    | cons p slots ih =>
        exact ih _ (d.executeSlot_thermalIntegrable p.1 p.2 st hstate)
  exact hfold _ initial hi

theorem state_thermalIntegrable (initial : FiniteRepairState)
    (hi : initial.ThermalIntegrable) (k : ℕ) :
    (d.state initial k).ThermalIntegrable := by
  simpa only [partialState_zero] using d.partialState_thermalIntegrable initial hi k 0

theorem partialState_front_ge_initial (initial : FiniteRepairState) (k r : ℕ) (j : ℤ) :
    initial.front j ≤ (d.partialState initial k r).front j := by
  rw [d.partialState_eq_fold]
  exact front_le_foldl FiniteRepairState.front _
    (fun st p j => executeSlot_front_mono_of_update p.1 FiniteRepairState.front
      (d.step p.1) (d.step_front_mono p.1) p.2 st j) initial _ j

end RealTailLocalData
end GapFamily.Construction
