import GapFamily.Construction.InitialReferenceCellRepairDatum
import GapFamily.Construction.FiniteRepairHistory
import GapFamily.Construction.FiniteRepairState

/-! The literal finite history and unit-node list of the actual initial cells. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Classical

namespace GapFamily.Construction
open Analytic

private theorem sum_selected_row {S : Finset ℤ} {M : Type*} [AddCommMonoid M]
    (f : S → M) (j : ℤ) :
    (∑ J : S, if j = (J : ℤ) then f J else 0) =
      if hj : j ∈ S then f ⟨j, hj⟩ else 0 := by
  by_cases hj : j ∈ S
  · rw [dite_eq_left hj]
    let J0 : S := ⟨j, hj⟩
    have he (J : S) : j = (J : ℤ) ↔ J0 = J := by
      constructor
      · exact fun h => Subtype.ext h
      · exact fun h => congrArg Subtype.val h
    simp_rw [he]
    simp [J0]
  · rw [dite_eq_right hj]
    apply Finset.sum_eq_zero
    intro J _
    exact ite_eq_right (fun h : j = (J : ℤ) => hj (h.symm ▸ J.property))

private theorem list_sum_flatMap {A M : Type*} [AddCommMonoid M]
    (L : List A) (f : A → List M) :
    (L.flatMap f).sum = (L.map (fun x => (f x).sum)).sum := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

variable (S : Finset ℤ) (b U : ℝ) (k : ℕ) (q : ℤ → ℝ → ℝ)
  (cells : ∀ J : S, InitialReferenceCell (J : ℤ) (max b |(J : ℝ)|) U k
    (q J))

/-- The list retains every actual initial-cell repair, with its common cutoff. -/
def realInitialRepairHistory (B0 : ℝ) (hB0 : 1 ≤ B0)
    (hcut : ∀ J, (cells J).right < B0) : List CanonicalRepairDatum :=
  S.attach.toList.map (fun J =>
    (cells J).repairDatum B0 hB0 (le_max_right _ _) (hcut J))

/-- A literal list of unit-node occurrences, retaining repeated nodes. -/
def realInitialRepairNodes : List (ℝ × ℤ) :=
  S.attach.toList.flatMap (fun J => List.ofFn (fun i => ((cells J).node i, (J : ℤ))))

theorem realInitialRepairHistory_cutoff (B0 : ℝ) (hB0 : 1 ≤ B0)
    (hcut : ∀ J, (cells J).right < B0) (D : CanonicalRepairDatum)
    (hD : D ∈ realInitialRepairHistory S b U k q cells B0 hB0 hcut) : D.cutoffB = B0 := by
  obtain ⟨J, _, rfl⟩ := List.mem_map.mp hD
  rfl

/-- The history seed is exactly the finite sum of the selected cell seeds. -/
theorem repairHistorySeed_realInitialRepairHistory (B0 : ℝ) (hB0 : 1 ≤ B0)
    (hcut : ∀ J, (cells J).right < B0) (τ : UpperHalfPlane) :
    repairHistorySeed (realInitialRepairHistory S b U k q cells B0 hB0 hcut) τ =
      ∑ J : S, (cells J).repairSeed B0 hB0 (le_max_right _ _) (hcut J) τ := by
  simp only [repairHistorySeed, realInitialRepairHistory, List.map_map, Function.comp_def,
    Finset.sum_map_toList, Finset.attach_eq_univ, InitialReferenceCell.repairDatum_seed]

/-- The same list gives the finite sum of the actual ordinary cell outputs. -/
theorem repairHistoryThermalOutput_realInitialRepairHistory (B0 : ℝ) (hB0 : 1 ≤ B0)
    (hcut : ∀ J, (cells J).right < B0) (j : ℤ) (t : ℝ) :
    repairHistoryThermalOutput (realInitialRepairHistory S b U k q cells B0 hB0 hcut) j t =
      ∑ J : S, (cells J).repairOutput B0 hB0 (le_max_right _ _) (hcut J) j t := by
  simp only [repairHistoryThermalOutput, realInitialRepairHistory, List.map_map, Function.comp_def,
    Finset.sum_map_toList, Finset.attach_eq_univ, InitialReferenceCell.repairDatum_thermalOutput]

/-- Each raw row is exactly its selected residual and vanishes outside the family. -/
theorem repairHistoryRawInput_realInitialRepairHistory (B0 : ℝ) (hB0 : 1 ≤ B0)
    (hcut : ∀ J, (cells J).right < B0) (j : ℤ) :
    repairHistoryRawInput (realInitialRepairHistory S b U k q cells B0 hB0 hcut) j =
      if hj : j ∈ S then (cells ⟨j, hj⟩).residual else 0 := by
  have he (J : S) :
      (if j ∈ lowBandSpinSet B0 then (cells J).rowInput j else 0) =
        if j = (J : ℤ) then (cells J).residual else 0 := by
    by_cases hj : j = (J : ℤ)
    · subst j
      simp [(cells J).input_spin_mem B0 (le_max_right _ _) (hcut J)]
    · simp [InitialReferenceCell.rowInput, hj]
  simp only [repairHistoryRawInput, realInitialRepairHistory, List.map_map, Function.comp_apply,
    InitialReferenceCell.repairDatum_cutoffB, InitialReferenceCell.repairDatum_input,
    Finset.sum_map_toList, Finset.attach_eq_univ]
  change (∑ J : S, if j ∈ lowBandSpinSet B0 then (cells J).rowInput j else 0) = _
  simp_rw [he]
  exact sum_selected_row (fun J => (cells J).residual) j

/-- The flattened node list is the sum of the literal unit-node Dirac measures. -/
theorem unitNodeRowThermalMeasure_realInitialRepairNodes_sum (j : ℤ) (t : ℝ) :
    unitNodeRowThermalMeasure (realInitialRepairNodes S b U k q cells) j t =
      ∑ J : S, if j = (J : ℤ) then
        ∑ i, VectorMeasure.dirac ((cells J).node i) (Real.exp (-t * (cells J).node i)) else 0 := by
  simp only [unitNodeRowThermalMeasure, realInitialRepairNodes, List.map_flatMap, list_sum_flatMap,
    List.map_ofFn, List.sum_ofFn, Finset.sum_map_toList, Finset.attach_eq_univ,
    Function.comp_apply]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hj : j = (J : ℤ)
  · subst j
    simp
  · simp [hj, Ne.symm hj]

theorem unitNodeRowThermalMeasure_realInitialRepairNodes (j : ℤ) (t : ℝ) :
    unitNodeRowThermalMeasure (realInitialRepairNodes S b U k q cells) j t =
      if hj : j ∈ S then
        ∑ i, VectorMeasure.dirac ((cells ⟨j, hj⟩).node i)
          (Real.exp (-t * (cells ⟨j, hj⟩).node i)) else 0 := by
  rw [unitNodeRowThermalMeasure_realInitialRepairNodes_sum]
  exact sum_selected_row _ j

/-- Every recorded node is physical and lies below its actual repair cutoff. -/
theorem realInitialRepairNodes_physical (B0 : ℝ) (hcut : ∀ J, (cells J).right < B0)
    (p : ℝ × ℤ) (hp : p ∈ realInitialRepairNodes S b U k q cells) :
    |(p.2 : ℝ)| ≤ p.1 ∧ p.1 < B0 := by
  obtain ⟨J, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨(le_max_right _ _).trans ((cells J).node_mem i).1,
    ((cells J).node_mem i).2.trans_lt (hcut J)⟩

/-- The actual thermal history has precisely the recorded unit-node atoms. -/
theorem repairHistoryThermalOutput_realInitialRepairHistory_singleton
    (B0 : ℝ) (hB0 : 1 ≤ B0) (hcut : ∀ J, (cells J).right < B0)
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    repairHistoryThermalOutput (realInitialRepairHistory S b U k q cells B0 hB0 hcut) j t {e} =
      unitNodeRowThermalMeasure (realInitialRepairNodes S b U k q cells) j t {e} := by
  rw [repairHistoryThermalOutput_singleton _ j ht e,
    repairHistoryRawInput_realInitialRepairHistory, unitNodeRowThermalMeasure_realInitialRepairNodes]
  by_cases hj : j ∈ S
  · simp only [dite_eq_left hj, InitialReferenceCell.residual_singleton, Finset.mul_sum]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    by_cases he : (cells ⟨j, hj⟩).node i = e
    · simp [he, VectorMeasure.dirac]
    · simp [he, VectorMeasure.dirac]
  · simp [hj]

end GapFamily.Construction
