import GapFamily.Regrouping
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite integer layers

This module isolates the combinatorial part of the marker construction: one marker,
a finite initial block, and a finite block per natural-number layer. The lower bound
`m ≤ E` on layer `m` implies local finiteness before coincident nodes are regrouped.
-/

namespace GapFamily.Layer

/-- Each unit node retains its origin, even if its coordinate repeats. -/
abbrev Node (initialCount : ℕ) (layerCount : ℕ → ℕ) :=
  Unit ⊕ (Fin initialCount ⊕ (Σ m : ℕ, Fin (layerCount m)))

/-- The marker node cannot be lost when subsequent blocks are added. -/
def marker (initialCount : ℕ) (layerCount : ℕ → ℕ) : Node initialCount layerCount :=
  Sum.inl ()

/-- Energy on the disjoint union of the marker, initial nodes, and layer nodes. -/
def energy {initialCount : ℕ} {layerCount : ℕ → ℕ} (markerEnergy : ℝ)
    (initialEnergy : Fin initialCount → ℝ) (layerEnergy : ∀ m, Fin (layerCount m) → ℝ) :
    Node initialCount layerCount → ℝ :=
  Sum.elim (fun _ ↦ markerEnergy) (Sum.elim initialEnergy (fun p ↦ layerEnergy p.1 p.2))

@[simp] theorem energy_marker {initialCount : ℕ} {layerCount : ℕ → ℕ}
    (markerEnergy : ℝ) (initialEnergy : Fin initialCount → ℝ)
    (layerEnergy : ∀ m, Fin (layerCount m) → ℝ) :
    energy markerEnergy initialEnergy layerEnergy (marker initialCount layerCount) =
      markerEnergy := rfl

/-- A finite number of layers contains only finitely many unit nodes. -/
theorem finite_layer_sublevel {layerCount : ℕ → ℕ}
    (layerEnergy : ∀ m, Fin (layerCount m) → ℝ)
    (hlower : ∀ (m : ℕ) i, (m : ℝ) ≤ layerEnergy m i) (bound : ℝ) :
    {p : Σ m : ℕ, Fin (layerCount m) | layerEnergy p.1 p.2 ≤ bound}.Finite := by
  have hfinite : (⋃ m : ℕ, ⋃ (_ : m ∈ {m : ℕ | m ≤ ⌊bound⌋₊}),
      Set.range (fun i : Fin (layerCount m) ↦ (⟨m, i⟩ : Σ n : ℕ, Fin (layerCount n)))).Finite :=
    (Set.finite_le_nat ⌊bound⌋₊).biUnion fun m _ ↦ Set.finite_range (fun i : Fin (layerCount m) ↦ (⟨m, i⟩ : Σ n : ℕ, Fin (layerCount n)))
  apply hfinite.subset
  rintro ⟨m, i⟩ hi
  exact Set.mem_iUnion₂.mpr ⟨m, Nat.le_floor ((hlower m i).trans hi), i, rfl⟩

/-- Finite initial data and escaping finite layers yield a locally finite unit spectrum. -/
theorem finite_energy_sublevel {initialCount : ℕ} {layerCount : ℕ → ℕ}
    (markerEnergy : ℝ) (initialEnergy : Fin initialCount → ℝ)
    (layerEnergy : ∀ m, Fin (layerCount m) → ℝ)
    (hlower : ∀ (m : ℕ) i, (m : ℝ) ≤ layerEnergy m i) (bound : ℝ) :
    {i : Node initialCount layerCount |
      energy markerEnergy initialEnergy layerEnergy i ≤ bound}.Finite := by
  rw [← Set.finite_preimage_inl_and_inr]
  constructor
  · exact Set.toFinite _
  · rw [← Set.finite_preimage_inl_and_inr]
    constructor
    · exact Set.toFinite _
    · exact finite_layer_sublevel layerEnergy hlower bound

/-- A constant shift from energy to dimension transports the local-finiteness result. -/
theorem locallyFinite_coordinate {initialCount : ℕ} {layerCount : ℕ → ℕ} {κ : Type*}
    (markerEnergy : ℝ) (initialEnergy : Fin initialCount → ℝ)
    (layerEnergy : ∀ m, Fin (layerCount m) → ℝ)
    (hlower : ∀ (m : ℕ) i, (m : ℝ) ≤ layerEnergy m i)
    (coordinate : Node initialCount layerCount → κ) (dimension : κ → ℝ)
    (shift : ℝ)
    (hdimension : ∀ i, dimension (coordinate i) =
      shift + energy markerEnergy initialEnergy layerEnergy i) :
    Regrouping.LocallyFinite coordinate dimension := by
  intro bound
  apply (finite_energy_sublevel markerEnergy initialEnergy layerEnergy hlower (bound - shift)).subset
  intro i hi
  change dimension (coordinate i) ≤ bound at hi
  change energy markerEnergy initialEnergy layerEnergy i ≤ bound - shift
  rw [hdimension] at hi
  linarith

/-- Every assertion verified on all three blocks holds on the full node spectrum. -/
theorem energy_property {initialCount : ℕ} {layerCount : ℕ → ℕ}
    (markerEnergy : ℝ) (initialEnergy : Fin initialCount → ℝ)
    (layerEnergy : ∀ m, Fin (layerCount m) → ℝ) (P : ℝ → Prop)
    (hmarker : P markerEnergy) (hinitial : ∀ i, P (initialEnergy i))
    (hlayer : ∀ m i, P (layerEnergy m i)) :
    ∀ i, P (energy markerEnergy initialEnergy layerEnergy i) := by
  rintro (i | i | ⟨m, i⟩)
  · exact hmarker
  · exact hinitial i
  · exact hlayer m i

/-- The layer data supply a countable index type, including repeated coordinates. -/
theorem node_countable (initialCount : ℕ) (layerCount : ℕ → ℕ) :
    Countable (Node initialCount layerCount) := inferInstance

/-- Absolute convergence on finite blocks and a summable layer total gives a genuine node sum. -/
theorem summable_node_norm {initialCount : ℕ} {layerCount : ℕ → ℕ}
    {A : Type*} [NormedAddCommGroup A] (term : Node initialCount layerCount → A)
    (hlayer : Summable (fun m ↦ ∑ i : Fin (layerCount m),
      ‖term (Sum.inr (Sum.inr ⟨m, i⟩))‖)) :
    Summable (fun i ↦ ‖term i‖) := by
  have htail : Summable (fun p : Σ m : ℕ, Fin (layerCount m) ↦
      ‖term (Sum.inr (Sum.inr p))‖) := by
    apply (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).2
    refine ⟨fun m ↦ Summable.of_finite, ?_⟩
    simpa only [tsum_fintype] using hlayer
  exact Summable.sum _ (Summable.of_finite) (Summable.sum _ (Summable.of_finite) htail)

/-- A complete target space admits the full node series once the layer norm totals converge. -/
theorem summable_node {initialCount : ℕ} {layerCount : ℕ → ℕ}
    {A : Type*} [NormedAddCommGroup A] [CompleteSpace A]
    (term : Node initialCount layerCount → A)
    (hlayer : Summable (fun m ↦ ∑ i : Fin (layerCount m),
      ‖term (Sum.inr (Sum.inr ⟨m, i⟩))‖)) : Summable term :=
  (summable_node_norm term hlayer).of_norm

/-- One deterministic slot leaves a cleared front fixed, and otherwise selects an endpoint. -/
noncomputable def slot (m : ℝ) (select : ℝ → ℝ) (front : ℝ) : ℝ :=
  if m + 1 ≤ front then front else select front

/-- A slot preserves the front when every executed cell advances by at least one half. -/
theorem front_le_slot {m front : ℝ} (select : ℝ → ℝ) (hfront : m ≤ front)
    (hselect : ∀ L, m ≤ L → L < m + 1 → L + 1 / 2 ≤ select L) :
    front ≤ slot m select front := by
  unfold slot
  split_ifs with h
  · exact le_rfl
  · have := hselect front hfront (lt_of_not_ge h)
    linarith

/-- Two predetermined slots suffice to advance every row from layer `m` to `m + 1`. -/
theorem two_slots_advance {m front : ℝ} (first second : ℝ → ℝ) (hfront : m ≤ front)
    (hfirstSelect : ∀ L, m ≤ L → L < m + 1 → L + 1 / 2 ≤ first L)
    (hsecondSelect : ∀ L, m ≤ L → L < m + 1 → L + 1 / 2 ≤ second L) :
    m + 1 ≤ slot m second (slot m first front) := by
  by_cases hfirst : m + 1 ≤ front
  · simp only [slot, ite_eq_left hfirst]
    exact hfirst
  · have hstep := hfirstSelect front hfront (lt_of_not_ge hfirst)
    have hnext : m ≤ first front := by linarith
    simp only [slot, ite_eq_right hfirst]
    split_ifs with hsecond
    · exact hsecond
    · have hstep' := hsecondSelect (first front) hnext (lt_of_not_ge hsecond)
      linarith

/-- Two predetermined slots for each row in an integer layer. -/
abbrev Slot (m : ℕ) := Fin (2 * m + 1) × Fin 2

/-- The slot index has exactly the cardinality used in the error estimate. -/
theorem slot_card (m : ℕ) : Fintype.card (Slot m) = 4 * m + 2 := by
  simp only [Slot, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The allowed error of one slot in layer `m`, with the frozen construction's normalization. -/
noncomputable def slotBudget (m : ℕ) : ℝ :=
  1 / (512 * (2 * (m : ℝ) + 1) * (m + 1) * (m + 2))

/-- There are two slots for each of the `2m + 1` integer spins. -/
noncomputable def layerBudget (m : ℕ) : ℝ := (4 * (m : ℝ) + 2) * slotBudget m

/-- Summing the same allowance over the actual finite slot index gives the layer allowance. -/
theorem sum_slotBudget (m : ℕ) : (∑ _ : Slot m, slotBudget m) = layerBudget m := by
  rw [Finset.sum_const, Finset.card_univ, slot_card, nsmul_eq_mul]
  simp only [layerBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

/-- The entire layer cost is a telescoping difference. -/
theorem layerBudget_eq (m : ℕ) :
    layerBudget m = (1 / 256 : ℝ) * (1 / (m + 1) - 1 / (m + 2)) := by
  have h1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (m : ℝ) + 2 ≠ 0 := by positivity
  have h3 : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  unfold layerBudget slotBudget
  field_simp
  ring

/-- Every finite initial collection of layers has the exact cumulative error stated here. -/
theorem sum_layerBudget (n : ℕ) :
    (∑ m ∈ Finset.range n, layerBudget m) =
      (1 / 256 : ℝ) * (1 - 1 / ((n : ℝ) + 1)) := by
  simp_rw [layerBudget_eq]
  rw [← Finset.mul_sum]
  congr 1
  have h := Finset.sum_range_sub' (fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1)) n
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_div_one,
    add_assoc, one_add_one_eq_two] using h

/-- The budget is bounded before the infinite construction is taken. -/
theorem sum_layerBudget_le (n : ℕ) :
    (∑ m ∈ Finset.range n, layerBudget m) ≤ (1 / 256 : ℝ) := by
  rw [sum_layerBudget]
  have h : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  linarith

/-- All layer errors are nonnegative. -/
theorem layerBudget_nonneg (m : ℕ) : 0 ≤ layerBudget m := by
  unfold layerBudget slotBudget
  positivity

/-- The layer majorant is summable, as required for the modular-correction limit. -/
theorem summable_layerBudget : Summable layerBudget :=
  summable_of_sum_range_le layerBudget_nonneg sum_layerBudget_le

/-- The complete infinite tail spends at most the fixed budget. -/
theorem tsum_layerBudget_le : (∑' m, layerBudget m) ≤ (1 / 256 : ℝ) :=
  Real.tsum_le_of_sum_range_le layerBudget_nonneg sum_layerBudget_le

/-- A pointwise correction estimate by the layer budget proves convergence of the correction sum. -/
theorem summable_correction {A : Type*} [NormedAddCommGroup A] [CompleteSpace A]
    (correction : ℕ → A) (majorant : ℝ)
    (hbound : ∀ m, ‖correction m‖ ≤ layerBudget m * majorant) : Summable correction :=
  (summable_layerBudget.mul_right majorant).of_norm_bounded hbound


end GapFamily.Layer
