import GapFamily.Construction.RealInitialStateHistory
import GapFamily.Construction.InitialReferenceCellRepairDensity
import GapFamily.Construction.FiniteRepairState

/-!
# The actual finite initial repair state

The initial cells give the same concrete repair history used in the tail
iteration. The reference density is cleared to each chosen front, and the
actual exterior responses of all initial repairs are retained above their
common cutoff.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace GapFamily.Construction

open Analytic

variable (S : Finset ℤ) (b U : ℝ) (k : ℕ) (q : ℤ → ℝ → ℝ)
  (cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) U k
    (q J))
  (B0 : ℝ) (hB0 : 1 ≤ B0) (hcut : ∀ J, (cells J).right < B0)

/-- The selected endpoint on repaired rows and the physical reference front elsewhere. -/
def realInitialRepairFront (j : ℤ) : ℝ :=
  if hj : j ∈ S then (cells ⟨j, hj⟩).right else max b |(j : ℝ)|

@[simp] theorem realInitialRepairFront_of_mem (j : ℤ) (hj : j ∈ S) :
    realInitialRepairFront S b U k q cells j = (cells ⟨j, hj⟩).right := by
  simp [realInitialRepairFront, hj]

@[simp] theorem realInitialRepairFront_of_notMem (j : ℤ) (hj : j ∉ S) :
    realInitialRepairFront S b U k q cells j = max b |(j : ℝ)| := by
  simp [realInitialRepairFront, hj]

theorem max_le_realInitialRepairFront (j : ℤ) :
    max b |(j : ℝ)| ≤ realInitialRepairFront S b U k q cells j := by
  by_cases hj : j ∈ S
  · rw [realInitialRepairFront_of_mem S b U k q cells j hj]
    exact (cells ⟨j, hj⟩).left_le_right
  · rw [realInitialRepairFront_of_notMem S b U k q cells j hj]

theorem realInitialRepairFront_lt_cutoff (hcut : ∀ J, (cells J).right < B0)
    (j : ℤ) (hj : j ∈ S) :
    realInitialRepairFront S b U k q cells j < B0 := by
  rw [realInitialRepairFront_of_mem S b U k q cells j hj]
  exact hcut ⟨j, hj⟩

/-- Covering the required initial rows makes every front exceed the common threshold. -/
theorem max_le_realInitialRepairFront_of_cover (T : ℝ) (hTU : T ≤ U)
    (hcover : ∀ j : ℤ, |(j : ℝ)| ≤ T → j ∈ S) (j : ℤ) :
    max T |(j : ℝ)| ≤ realInitialRepairFront S b U k q cells j := by
  apply max_le
  · by_cases hj : j ∈ S
    · rw [realInitialRepairFront_of_mem S b U k q cells j hj]
      exact hTU.trans (cells ⟨j, hj⟩).right_mem.1
    · have hT : T < |(j : ℝ)| := lt_of_not_ge (fun h => hj (hcover j h))
      exact hT.le.trans ((le_max_right b _).trans
        (max_le_realInitialRepairFront S b U k q cells j))
  · exact (le_max_right b _).trans (max_le_realInitialRepairFront S b U k q cells j)

theorem realInitialRepairFront_mem_window (j : ℤ) (hj : j ∈ S) :
    realInitialRepairFront S b U k q cells j ∈ Icc U (U + 1) := by
  rw [realInitialRepairFront_of_mem S b U k q cells j hj]
  exact (cells ⟨j, hj⟩).right_mem

/-- The literal finite sum of the actual exterior repair numerators. -/
def realInitialRepairExterior (j : ℤ) (e : ℝ) : ℝ :=
  ∑ J : S, if B0 < e then (cells J).exteriorNumerator B0 hB0 j e else 0

theorem realInitialRepairExterior_eq_zero (j : ℤ) (e : ℝ) (he : e ≤ B0) :
    realInitialRepairExterior S b U k q cells B0 hB0 j e = 0 := by
  simp [realInitialRepairExterior, not_lt.mpr he]

/-- The representative of the actual initial continuum, cleared pointwise below its front. -/
def realInitialRepairNumerator (j : ℤ) (e : ℝ) : ℝ :=
  if e < realInitialRepairFront S b U k q cells j then 0 else
    q j e +
      realInitialRepairExterior S b U k q cells B0 hB0 j e

/-- The initial state uses the literal finite history of the actual cell repairs. -/
def realInitialRepairState : FiniteRepairState where
  front := realInitialRepairFront S b U k q cells
  nodes := realInitialRepairNodes S b U k q cells
  numerator := realInitialRepairNumerator S b U k q cells B0 hB0
  history := realInitialRepairHistory S b U k q cells B0 hB0 hcut

@[simp] theorem realInitialRepairState_front :
    (realInitialRepairState S b U k q cells B0 hB0 hcut).front =
      realInitialRepairFront S b U k q cells := rfl

@[simp] theorem realInitialRepairState_nodes :
    (realInitialRepairState S b U k q cells B0 hB0 hcut).nodes =
      realInitialRepairNodes S b U k q cells := rfl

@[simp] theorem realInitialRepairState_numerator :
    (realInitialRepairState S b U k q cells B0 hB0 hcut).numerator =
      realInitialRepairNumerator S b U k q cells B0 hB0 := rfl

@[simp] theorem realInitialRepairState_history :
    (realInitialRepairState S b U k q cells B0 hB0 hcut).history =
      realInitialRepairHistory S b U k q cells B0 hB0 hcut := rfl

/-- Every recorded occurrence is an actual physical initial node at or below its chosen front. -/
theorem realInitialRepairState_node_position (p : ℝ × ℤ)
    (hp : p ∈ (realInitialRepairState S b U k q cells B0 hB0 hcut).nodes) :
    p.2 ∈ S ∧ max b |(p.2 : ℝ)| ≤ p.1 ∧
      p.1 ≤ (realInitialRepairState S b U k q cells B0 hB0 hcut).front p.2 := by
  obtain ⟨J, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  refine ⟨J.property, ((cells J).node_mem i).1, ?_⟩
  change (cells J).node i ≤ realInitialRepairFront S b U k q cells (J : ℤ)
  rw [realInitialRepairFront_of_mem S b U k q cells J J.property]
  exact ((cells J).node_mem i).2

/-- Every physical row is pointwise cleared below its actual initial front. -/
theorem realInitialRepairState_cleared :
    (realInitialRepairState S b U k q cells B0 hB0 hcut).Cleared := by
  intro j e _ he
  exact ite_eq_left he

/-- On every unprocessed energy the numerator retains the actual reference and repair errors. -/
theorem realInitialRepairNumerator_eq (j : ℤ) (e : ℝ)
    (he : realInitialRepairFront S b U k q cells j ≤ e) :
    realInitialRepairNumerator S b U k q cells B0 hB0 j e =
      q j e +
        realInitialRepairExterior S b U k q cells B0 hB0 j e :=
  ite_eq_right (not_lt.mpr he)

/-- The finite exterior error is bounded by the actual sum of absolute row errors. -/
theorem abs_realInitialRepairExterior_le (j : ℤ) (e : ℝ) :
    |realInitialRepairExterior S b U k q cells B0 hB0 j e| ≤
      ∑ J : S, |if B0 < e then (cells J).exteriorNumerator B0 hB0 j e else 0| :=
  Finset.abs_sum_le_sum_abs _ _

/-- The initial reference half-budget and initial repair eighth-budget leave `5H/8`. -/
theorem realInitialRepairNumerator_error_le_five_eighths
    (target H : ℤ → ℝ → ℝ) (j : ℤ) (e : ℝ)
    (he : realInitialRepairFront S b U k q cells j ≤ e)
    (href : |q j e - target j e| ≤ H j e / 2)
    (hrepair : (∑ J : S, |if B0 < e then (cells J).exteriorNumerator B0 hB0 j e else 0|) ≤
      H j e / 8) :
    |realInitialRepairNumerator S b U k q cells B0 hB0 j e - target j e| ≤
      5 * H j e / 8 := by
  rw [realInitialRepairNumerator_eq S b U k q cells B0 hB0 j e he]
  have hs := (abs_realInitialRepairExterior_le S b U k q cells B0 hB0 j e).trans hrepair
  calc
    _ = |(q j e - target j e) +
        realInitialRepairExterior S b U k q cells B0 hB0 j e| := by congr 1; ring
    _ ≤ |q j e - target j e| +
        |realInitialRepairExterior S b U k q cells B0 hB0 j e| := abs_add_le _ _
    _ ≤ H j e / 2 + H j e / 8 := add_le_add href hs
    _ = _ := by ring

end GapFamily.Construction
