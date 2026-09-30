import GapFamily.Construction.RealInitialState
import GapFamily.Construction.LayerScheduleBlock

/-! Front and node bounds for the actual initial repair state. The selected
cell endpoint lies in its prescribed unit window, and every recorded node
occurrence lies below that endpoint. -/

noncomputable section

open Set

namespace GapFamily.Construction

open Analytic

variable (S : Finset ℤ) (b U : ℝ) (k : ℕ) (q : ℤ → ℝ → ℝ)
  (cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) U k
    (q J))
  (B0 : ℝ) (hB0 : 1 ≤ B0) (hcut : ∀ J, (cells J).right < B0)

/-- Repaired rows end within the actual selected endpoint window. -/
theorem realInitialRepairFront_le_upper_of_mem (j : ℤ) (hj : j ∈ S) :
    realInitialRepairFront S b U k q cells j ≤ U + 1 :=
  (realInitialRepairFront_mem_window S b U k q cells j hj).2

/-- The physical reference front on unselected rows obeys the same common bound. -/
theorem realInitialRepairFront_le_max (hbU : b ≤ U + 1) (j : ℤ) :
    realInitialRepairFront S b U k q cells j ≤ max (U + 1) |(j : ℝ)| := by
  by_cases hj : j ∈ S
  · exact (realInitialRepairFront_le_upper_of_mem S b U k q cells j hj).trans
      (le_max_left _ _)
  · rw [realInitialRepairFront_of_notMem S b U k q cells j hj]
    exact max_le_max hbU le_rfl

theorem realInitialRepairState_front_le_max (hbU : b ≤ U + 1) (j : ℤ) :
    (realInitialRepairState S b U k q cells B0 hB0 hcut).front j ≤
      max (U + 1) |(j : ℝ)| :=
  realInitialRepairFront_le_max S b U k q cells hbU j

include cells in
/-- One actual selected cell forces the reference threshold below the window. -/
theorem realInitialRepairThreshold_le_upper_of_nonempty (hS : S.Nonempty) : b ≤ U + 1 := by
  obtain ⟨J, hJ⟩ := hS
  exact (le_max_left b |(J : ℝ)|).trans
    ((cells ⟨J, hJ⟩).left_le_right.trans (cells ⟨J, hJ⟩).right_mem.2)

theorem realInitialRepairState_front_le_max_of_nonempty (hS : S.Nonempty) (j : ℤ) :
    (realInitialRepairState S b U k q cells B0 hB0 hcut).front j ≤
      max (U + 1) |(j : ℝ)| :=
  realInitialRepairState_front_le_max S b U k q cells B0 hB0 hcut
    (realInitialRepairThreshold_le_upper_of_nonempty S b U k q cells hS) j

/-- The actual initial front meets the upper comparison at the start of any layer. -/
theorem realInitialRepairState_front_le_layer_start (hS : S.Nonempty) (m : ℕ) (j : ℤ) :
    (realInitialRepairState S b U k q cells B0 hB0 hcut).front j ≤
      max (U + 1) (max ((m : ℝ) + 1) |(j : ℝ)|) :=
  (realInitialRepairState_front_le_max_of_nonempty S b U k q cells B0 hB0 hcut hS j).trans
    (max_le_max le_rfl (le_max_right _ _))

/-- Every literal initial node occurrence lies below its cell's selected endpoint. -/
theorem realInitialRepairNodes_energy_le (p : ℝ × ℤ)
    (hp : p ∈ realInitialRepairNodes S b U k q cells) : p.1 ≤ U + 1 := by
  obtain ⟨J, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact ((cells J).node_mem i).2.trans (cells J).right_mem.2

theorem realInitialRepairState_node_energy_le (p : ℝ × ℤ)
    (hp : p ∈ (realInitialRepairState S b U k q cells B0 hB0 hcut).nodes) :
    p.1 ≤ U + 1 :=
  realInitialRepairNodes_energy_le S b U k q cells p hp

/-- Strict quadrature keeps every occurrence away from its physical left
endpoint and its selected right endpoint. -/
theorem realInitialRepairState_node_position_strict (p : ℝ × ℤ)
    (hp : p ∈ (realInitialRepairState S b U k q cells B0 hB0 hcut).nodes) :
    p.2 ∈ S ∧ max b |(p.2 : ℝ)| < p.1 ∧
      p.1 < (realInitialRepairState S b U k q cells B0 hB0 hcut).front p.2 := by
  obtain ⟨J, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  refine ⟨J.property, ((cells J).node_strict i).1, ?_⟩
  change (cells J).node i < realInitialRepairFront S b U k q cells (J : ℤ)
  rw [realInitialRepairFront_of_mem S b U k q cells J J.property]
  exact ((cells J).node_strict i).2

/-- The cutoff and marker may be different, including a marker at zero. -/
theorem realInitialRepairState_node_strict {δ : ℝ} (hδ : δ ≤ b) (p : ℝ × ℤ)
    (hp : p ∈ (realInitialRepairState S b U k q cells B0 hB0 hcut).nodes) :
    δ < p.1 :=
  (hδ.trans (le_max_left _ _)).trans_lt
    (realInitialRepairState_node_position_strict S b U k q cells B0 hB0 hcut p hp).2.1

/-- The same literal occurrence obeys both the marker separation and the
physical spin cone needed by permanent-spectrum regrouping. -/
theorem realInitialRepairState_node_spectrum_bounds {δ : ℝ} (hδ : δ ≤ b) (p : ℝ × ℤ)
    (hp : p ∈ (realInitialRepairState S b U k q cells B0 hB0 hcut).nodes) :
    δ < p.1 ∧ |(p.2 : ℝ)| ≤ p.1 := by
  have h := (realInitialRepairState_node_position_strict S b U k q cells B0 hB0 hcut p hp).2.1
  exact ⟨(hδ.trans (le_max_left _ _)).trans_lt h, (le_max_right _ _).trans h.le⟩

/-- Every initial cell lies below the standard repair band `2U + 4`. -/
theorem realInitialRepairCell_right_lt_band (hU : 0 ≤ U) (J : S) :
    (cells J).right < 2 * U + 4 := by
  linarith [(cells J).right_mem.2]

/-- The common real-parameter initial band is admissible. -/
theorem realInitialRepairBand_one (hU : 0 ≤ U) : 1 ≤ 2 * U + 4 := by linarith

/-- The initial finite node list is strictly below every later layer cutoff. -/
theorem realInitialRepairNodes_lt_layerCutoff (m : ℕ) (p : ℝ × ℤ)
    (hp : p ∈ realInitialRepairNodes S b U k q cells) : p.1 < layerCutoff U m :=
  lt_layerCutoff_of_initial_upper (realInitialRepairNodes_energy_le S b U k q cells p hp)

theorem realInitialRepairState_node_lt_layerCutoff (m : ℕ) (p : ℝ × ℤ)
    (hp : p ∈ (realInitialRepairState S b U k q cells B0 hB0 hcut).nodes) :
    p.1 < layerCutoff U m :=
  realInitialRepairNodes_lt_layerCutoff S b U k q cells m p hp

end GapFamily.Construction
