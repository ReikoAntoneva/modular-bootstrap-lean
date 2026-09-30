import GapFamily.Layer
import GapFamily.Construction.LayerBudgetTail
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Count

/-!
# The deterministic finite layer schedule

Layer `m` visits the integer rows `-m, ..., m` in increasing order and assigns
two consecutive slots to each row. Its literal list budget is the existing
telescoping layer budget; the schedule requires no cell endpoint assumption.
-/

namespace GapFamily.Construction

/-- The actual increasing list of rows visited in layer `m`. -/
def layerRows (m : ℕ) : List ℤ :=
  (List.range (2 * m + 1)).map (fun i : ℕ => (i : ℤ) - (m : ℤ))

/-- Exactly two consecutive slots are reserved for each row, in row order. -/
def layerSlots (m : ℕ) : List ℤ :=
  (layerRows m).flatMap (fun j => [j, j])

@[simp] theorem length_layerRows (m : ℕ) : (layerRows m).length = 2 * m + 1 := by
  simp [layerRows]

@[simp] theorem length_layerSlots (m : ℕ) : (layerSlots m).length = 4 * m + 2 := by
  have h (xs : List ℤ) : (xs.flatMap (fun j => [j, j])).length = 2 * xs.length := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih]; omega
  rw [layerSlots, h, length_layerRows]
  omega

@[simp] theorem mem_layerRows {m : ℕ} {j : ℤ} : j ∈ layerRows m ↔ |j| ≤ (m : ℤ) := by
  constructor
  · intro hj
    obtain ⟨i, hi, hij⟩ := List.mem_map.mp hj
    have hi' : i < 2 * m + 1 := List.mem_range.mp hi
    rw [← hij]
    apply abs_le.mpr
    constructor <;> omega
  · intro hj
    obtain ⟨hlo, hhi⟩ := abs_le.mp hj
    apply List.mem_map.mpr
    refine ⟨(j + (m : ℤ)).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega

@[simp] theorem mem_layerSlots (m : ℕ) (j : ℤ) : j ∈ layerSlots m ↔ |j| ≤ (m : ℤ) := by
  simp [layerSlots, mem_layerRows]

/-- The index formula fixes the deterministic row order. -/
theorem getElem_layerRows (m i : ℕ) (hi : i < (layerRows m).length) :
    (layerRows m)[i] = (i : ℤ) - (m : ℤ) := by
  simp only [layerRows, List.getElem_map, List.getElem_range]

/-- The actual finite row list is strictly increasing. -/
theorem pairwise_layerRows (m : ℕ) : (layerRows m).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [getElem_layerRows, getElem_layerRows]
  omega

theorem nodup_layerRows (m : ℕ) : (layerRows m).Nodup :=
  (pairwise_layerRows m).nodup

@[simp] theorem count_layerRows (m : ℕ) (j : ℤ) :
    (layerRows m).count j = if |j| ≤ (m : ℤ) then 1 else 0 := by
  simp [(nodup_layerRows m).count, mem_layerRows]

/-- Each visited spin occurs exactly twice, with no extra slot elsewhere. -/
@[simp] theorem count_layerSlots (m : ℕ) (j : ℤ) :
    (layerSlots m).count j = if |j| ≤ (m : ℤ) then 2 else 0 := by
  have h (xs : List ℤ) : (xs.flatMap (fun a => [a, a])).count j = 2 * xs.count j := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.flatMap_cons, List.count_append, List.count_cons, List.count_nil, ih]
      split <;> omega
  rw [layerSlots, h, count_layerRows]
  split <;> simp

/-- Summing the allowance on the literal slot list gives the frozen layer budget. -/
theorem sum_layerSlots_slotBudget (m : ℕ) :
    ((layerSlots m).map (fun _ => Layer.slotBudget m)).sum = Layer.layerBudget m := by
  simp [Layer.layerBudget, nsmul_eq_mul]

/-- The actual scheduled slots have the exact cumulative telescoping budget. -/
theorem sum_layerSlots_slotBudget_prefix (N : ℕ) :
    (∑ m ∈ Finset.range N, ((layerSlots m).map (fun _ => Layer.slotBudget m)).sum) =
      (1 / 256 : ℝ) * (1 - 1 / ((N : ℝ) + 1)) := by
  simp_rw [sum_layerSlots_slotBudget]
  exact Layer.sum_layerBudget N

theorem sum_layerSlots_slotBudget_prefix_le (N : ℕ) :
    (∑ m ∈ Finset.range N, ((layerSlots m).map (fun _ => Layer.slotBudget m)).sum) ≤
      (1 / 256 : ℝ) := by
  simp_rw [sum_layerSlots_slotBudget]
  exact Layer.sum_layerBudget_le N

/-- The actual sequence of finite-list budgets is ordinarily summable. -/
theorem summable_layerSlots_slotBudget :
    Summable (fun m : ℕ => ((layerSlots m).map (fun _ => Layer.slotBudget m)).sum) := by
  simpa only [sum_layerSlots_slotBudget] using Layer.summable_layerBudget

/-- The infinite deterministic schedule spends at most the fixed total error allowance. -/
theorem tsum_layerSlots_slotBudget_le :
    (∑' m : ℕ, ((layerSlots m).map (fun _ => Layer.slotBudget m)).sum) ≤ (1 / 256 : ℝ) := by
  simp_rw [sum_layerSlots_slotBudget]
  exact Layer.tsum_layerBudget_le

/-- Any finite consecutive block of actual scheduled slots has the exact
telescoping allowance of the corresponding layer block. -/
theorem sum_layerSlots_slotBudget_add (m N : ℕ) :
    (∑ n ∈ Finset.range N,
      ((layerSlots (m + n)).map (fun _ => Layer.slotBudget (m + n))).sum) =
      (1 / 256 : ℝ) * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + N + 1)) := by
  simp_rw [sum_layerSlots_slotBudget]
  exact sum_layerBudget_add m N

/-- The remaining deterministic schedule has a quantitative vanishing tail budget. -/
theorem tsum_layerSlots_slotBudget_add_le (m : ℕ) :
    (∑' n : ℕ, ((layerSlots (m + n)).map (fun _ => Layer.slotBudget (m + n))).sum) ≤
      (1 / 256 : ℝ) / ((m : ℝ) + 1) := by
  simp_rw [sum_layerSlots_slotBudget]
  exact tsum_layerBudget_add_le m

end GapFamily.Construction
