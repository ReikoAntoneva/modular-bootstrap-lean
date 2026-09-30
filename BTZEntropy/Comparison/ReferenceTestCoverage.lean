import GapFamily.Construction.RealTailCellThermal
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Exact coverage of each reference row by the literal finite tail cells.
The scheduler guards, failed local hypotheses, and repeated visits to a row
are retained throughout the finite telescoping identity. -/

noncomputable section

open Set MeasureTheory
open GapFamily.Analytic GapFamily.Construction
open scoped Classical

namespace BTZEntropy.Comparison

variable {μ : Measure ℝ} [NullSingletonClass μ]

theorem integral_Ioo_add_adjacent {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z)
    (g : ℝ → ℝ) (hg : IntegrableOn g (Ioo x z) μ) :
    (∫ E in Ioo x y, g E ∂μ) + (∫ E in Ioo y z, g E ∂μ) =
      ∫ E in Ioo x z, g E ∂μ := by
  rw [← setIntegral_union (by
    refine Set.disjoint_left.mpr ?_
    intro E hE hE'
    exact lt_asymm hE.2 hE'.1) measurableSet_Ioo
      (hg.mono_set (Ioo_subset_Ioo le_rfl hyz))
      (hg.mono_set (Ioo_subset_Ioo hxy le_rfl)),
    Ioo_union_Ioo_eq_Ioo_sdiff_singleton hxy hyz]
  exact setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton y))

/-- A finite nondecreasing sequence covers its total open interval, up to
the finitely many endpoints, which have zero mass. -/
theorem sum_integral_Ioo_adjacent (v : ℕ → ℝ) (hv : Monotone v)
    (g : ℝ → ℝ) (n : ℕ) (hg : IntegrableOn g (Ioo (v 0) (v n)) μ) :
    (∑ q : Fin n, ∫ E in Ioo (v q.val) (v (q.val + 1)), g E ∂μ) =
      ∫ E in Ioo (v 0) (v n), g E ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih (hg.mono_set (Ioo_subset_Ioo le_rfl (hv (Nat.le_succ n))))]
      exact integral_Ioo_add_adjacent (hv (Nat.zero_le n)) (hv (Nat.le_succ n)) g hg

variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
  (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)

/-- The contribution to one fixed reference row of an actual guarded slot. -/
def scheduledReferenceRowTest (j : ℤ) (g : ℝ → ℝ) (p : LayerSlotIndex T) : ℝ :=
  if p.row = j then
    ∫ E in layerSlotInterval T FiniteRepairState.front d.step initial p,
      g E ∂referenceMeasure j
  else 0

theorem scheduledReferenceRowTest_active (j : ℤ) (g : ℝ → ℝ)
    (p : d.ActiveSlot initial) :
    scheduledReferenceRowTest d initial j g p.val =
      if p.val.row = j then
        ∫ E in Ioo ((d.slotPreState initial p.val).front p.val.row)
          (d.activeCell initial p).right, g E ∂referenceMeasure j
      else 0 := by
  rw [scheduledReferenceRowTest, d.activeCell_interval_eq]

theorem scheduledReferenceRowTest_invalid (j : ℤ) (g : ℝ → ℝ)
    (p : LayerSlotIndex T)
    (hp : ¬RealTailStepValid a T (d.slotPreState initial p) p.layer p.row) :
    scheduledReferenceRowTest d initial j g p = 0 := by
  have hempty : layerSlotInterval T FiniteRepairState.front d.step initial p = ∅ :=
    layerSlotInterval_eq_empty_of_update_eq T FiniteRepairState.front d.step initial p
      (d.step_invalid hp)
  simp [scheduledReferenceRowTest, hempty]

/-- Other rows do not move at this slot, so inserting their zero interval
puts all slots into the same telescoping sum. -/
theorem scheduledReferenceRowTest_eq_frontIntegral (j : ℤ) (g : ℝ → ℝ)
    (p : LayerSlotIndex T) :
    scheduledReferenceRowTest d initial j g p =
      ∫ E in Ioo ((d.slotPreState initial p).front j)
        ((layerSlotPostState T FiniteRepairState.front d.step initial p).front j),
        g E ∂referenceMeasure j := by
  by_cases hp : p.row = j
  · simp [scheduledReferenceRowTest, layerSlotInterval, hp,
      RealTailLocalData.slotPreState]
  · have hfront :
        (layerSlotPostState T FiniteRepairState.front d.step initial p).front j =
          (d.slotPreState initial p).front j := by
      unfold layerSlotPostState executeSlot
      split_ifs
      · rfl
      · exact d.step_front_other _ _ _ (Ne.symm hp)
    simp [scheduledReferenceRowTest, hp, hfront]

/-- Every slot of one completed layer contributes precisely the difference
between the row front immediately before and after that layer. -/
theorem sum_scheduledReferenceRowTest_layer (j : ℤ) (g : ℝ → ℝ) (m : ℕ)
    (hg : IntegrableOn g
      (Ioo ((d.state initial m).front j) ((d.state initial (m + 1)).front j))
      (referenceMeasure j)) :
    (∑ q : Fin (layerSlots (T + m)).length,
      scheduledReferenceRowTest d initial j g ⟨m, q⟩) =
      ∫ E in Ioo ((d.state initial m).front j)
        ((d.state initial (m + 1)).front j), g E ∂referenceMeasure j := by
  let v : ℕ → ℝ := fun r => (d.partialState initial m r).front j
  have hv : Monotone v :=
    front_foldl_take_monotone FiniteRepairState.front _
      (fun s J i => executeSlot_front_mono_of_update (T + m)
        FiniteRepairState.front (d.step (T + m)) (d.step_front_mono (T + m)) J s i)
      _ _ j
  have hv0 : v 0 = (d.state initial m).front j := by simp [v]
  have hvlast : v (layerSlots (T + m)).length = (d.state initial (m + 1)).front j := by
    simp only [v, RealTailLocalData.partialState, List.take_length,
      RealTailLocalData.state, scheduledLayerState_succ_eq_slot_fold]
  calc
    _ = ∑ q : Fin (layerSlots (T + m)).length,
        ∫ E in Ioo (v q.val) (v (q.val + 1)), g E ∂referenceMeasure j := by
      apply Finset.sum_congr rfl
      intro q _
      rw [scheduledReferenceRowTest_eq_frontIntegral,
        layerSlotPostState_eq_take_succ]
      rfl
    _ = ∫ E in Ioo (v 0) (v (layerSlots (T + m)).length),
        g E ∂referenceMeasure j :=
      sum_integral_Ioo_adjacent v hv g _ (by simpa only [hv0, hvlast] using hg)
    _ = _ := by rw [hv0, hvlast]

/-- The actual finite tail cells cover the row from its initial front to
its current front. No interval coverage premise is assumed. -/
theorem sum_scheduledReferenceRowTest (j : ℤ) (g : ℝ → ℝ) (k : ℕ)
    (hg : IntegrableOn g
      (Ioo (initial.front j) ((d.state initial k).front j)) (referenceMeasure j)) :
    (∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
      scheduledReferenceRowTest d initial j g ⟨m, q⟩) =
      ∫ E in Ioo (initial.front j) ((d.state initial k).front j),
        g E ∂referenceMeasure j := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hmono := d.state_front_monotone initial j
      have hstart : initial.front j ≤ (d.state initial k).front j :=
        hmono (Nat.zero_le k)
      have hend := hmono (Nat.le_succ k)
      rw [Finset.sum_range_succ,
        ih (hg.mono_set (Ioo_subset_Ioo le_rfl hend)),
        sum_scheduledReferenceRowTest_layer d initial j g k
          (hg.mono_set (Ioo_subset_Ioo hstart le_rfl))]
      exact integral_Ioo_add_adjacent hstart hend g hg

/-- Once the final front lies beyond the support of the test, the same finite
sum is the entire open reference tail above the initial front. -/
theorem sum_scheduledReferenceRowTest_eq_tail (j : ℤ) (g : ℝ → ℝ) (k : ℕ)
    (hg : IntegrableOn g (Ioi (initial.front j)) (referenceMeasure j))
    (hzero : ∀ E, (d.state initial k).front j ≤ E → g E = 0) :
    (∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
      scheduledReferenceRowTest d initial j g ⟨m, q⟩) =
      ∫ E in Ioi (initial.front j), g E ∂referenceMeasure j := by
  rw [sum_scheduledReferenceRowTest d initial j g k
    (hg.mono_set (fun _ hE => hE.1))]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun _ hE => hE.1)
  intro E hE
  exact hzero E (not_lt.mp (fun hlt => hE.2 ⟨hE.1, hlt⟩))

/-- A global energy cutoff can be supplied independently of the current
front; only the verified front bound is needed to close the reference tail. -/
theorem sum_scheduledReferenceRowTest_eq_tail_of_cutoff
    (j : ℤ) (g : ℝ → ℝ) (k : ℕ) (R : ℝ)
    (hg : IntegrableOn g (Ioi (initial.front j)) (referenceMeasure j))
    (hzero : ∀ E, R ≤ E → g E = 0)
    (hfront : R ≤ (d.state initial k).front j) :
    (∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
      scheduledReferenceRowTest d initial j g ⟨m, q⟩) =
      ∫ E in Ioi (initial.front j), g E ∂referenceMeasure j :=
  sum_scheduledReferenceRowTest_eq_tail d initial j g k hg
    (fun E hE => hzero E (hfront.trans hE))

end BTZEntropy.Comparison
