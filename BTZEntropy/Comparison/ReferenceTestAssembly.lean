import BTZEntropy.Comparison.ReferenceTestBoundary
import BTZEntropy.Comparison.ReferenceTestCoverage
import BTZEntropy.Comparison.SpectrumTestSmooth
import BTZEntropy.Construction.FixedFamilyActual

/-! Exact comparison of the same actual spectral test with the integer-spin
leading reference. The initial-front boundary band is retained explicitly. -/

noncomputable section
open Set MeasureTheory Real
open GapFamily GapFamily.Analytic GapFamily.Construction
open BTZEntropy.Construction
open scoped BigOperators Classical

namespace BTZEntropy.Comparison

variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
  (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)

/-- Leading density on the actual interval traversed by a scheduler slot. -/
def scheduledLeadingCellTest (f : ℝ → ℝ) (p : LayerSlotIndex T) : ℝ :=
  scheduledReferenceRowTest d initial p.row (fun u => vacuumLeading a u p.row * f u) p

/-- The current density of the literal preceding state, on that same actual
interval. This is the continuum matched by the slot's quadrature nodes. -/
def scheduledCurrentCellTest (f : ℝ → ℝ) (p : LayerSlotIndex T) : ℝ :=
  scheduledReferenceRowTest d initial p.row
    (fun u => (d.slotPreState initial p).numerator p.row u * f u) p

theorem scheduledLeadingCellTest_active (f : ℝ → ℝ) (p : d.ActiveSlot initial) :
    scheduledLeadingCellTest d initial f p.val =
      ∫ u in Ioo ((d.slotPreState initial p.val).front p.val.row)
        (d.activeCell initial p).right,
        vacuumLeading a u p.val.row * f u ∂referenceMeasure p.val.row := by
  rw [scheduledLeadingCellTest, scheduledReferenceRowTest_active, ite_eq_left rfl]

theorem scheduledCurrentCellTest_active (f : ℝ → ℝ) (p : d.ActiveSlot initial) :
    scheduledCurrentCellTest d initial f p.val =
      ∫ u in Ioo ((d.slotPreState initial p.val).front p.val.row)
        (d.activeCell initial p).right,
        (d.slotPreState initial p.val).numerator p.val.row u * f u
          ∂referenceMeasure p.val.row := by
  rw [scheduledCurrentCellTest, scheduledReferenceRowTest_active, ite_eq_left rfl]

theorem scheduledLeadingCellTest_invalid (f : ℝ → ℝ) (p : LayerSlotIndex T)
    (hp : ¬RealTailStepValid a T (d.slotPreState initial p) p.layer p.row) :
    scheduledLeadingCellTest d initial f p = 0 :=
  scheduledReferenceRowTest_invalid d initial _ _ p hp

theorem scheduledCurrentCellTest_invalid (f : ℝ → ℝ) (p : LayerSlotIndex T)
    (hp : ¬RealTailStepValid a T (d.slotPreState initial p) p.layer p.row) :
    scheduledCurrentCellTest d initial f p = 0 :=
  scheduledReferenceRowTest_invalid d initial _ _ p hp

private theorem scheduledReferenceRowTest_summable (f : ℝ → ℝ) (p : LayerSlotIndex T) :
    Summable (fun j : ℤ => scheduledReferenceRowTest d initial j
      (fun u => vacuumLeading a u j * f u) p) := by
  apply summable_of_ne_finset_zero (s := {p.row})
  intro j hj
  have hne : p.row ≠ j := by simpa only [Finset.mem_singleton, ne_comm] using hj
  simp [scheduledReferenceRowTest, hne]

private theorem tsum_scheduledReferenceRowTest (f : ℝ → ℝ) (p : LayerSlotIndex T) :
    (∑' j : ℤ, scheduledReferenceRowTest d initial j
      (fun u => vacuumLeading a u j * f u) p) = scheduledLeadingCellTest d initial f p := by
  apply tsum_eq_single p.row
  intro j hj
  simp [scheduledReferenceRowTest, Ne.symm hj]

/-- Once the actual fronts pass the support cutoff, summing the true cell
intervals over every slot gives exactly the leading reference above the
actual initial fronts. The row/slot interchange is a proved finite sum. -/
theorem sum_scheduledLeadingCellTest_eq_tail {X : ℝ}
    (f : ℝ → ℝ) (hf : Continuous f) (hzero : ∀ u, X ≤ u → f u = 0)
    (ha : 2 ≤ a) (hT : (1 : ℝ) ≤ T)
    (hinitial : ∀ j : ℤ, max (T : ℝ) |(j : ℝ)| ≤ initial.front j)
    (k : ℕ) (hfront : ∀ j, X ≤ (d.state initial k).front j) :
    (∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
      scheduledLeadingCellTest d initial f ⟨m, q⟩) =
      ∑' j : ℤ, frontTailRowTest a initial.front f j := by
  have hrow (j : ℤ) := sum_scheduledReferenceRowTest_eq_tail_of_cutoff d initial j
    (fun u => vacuumLeading a u j * f u) k X
    ((integrableOn_leadingRowTest ha hT f hf hzero j).mono_set
      (Ioi_subset_Ioi (hinitial j)))
    (fun u hu => by rw [hzero u hu, mul_zero]) (hfront j)
  symm
  calc
    _ = ∑' j : ℤ, ∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
        scheduledReferenceRowTest d initial j
          (fun u => vacuumLeading a u j * f u) ⟨m, q⟩ := tsum_congr (fun j => (hrow j).symm)
    _ = ∑ m ∈ Finset.range k, ∑' j : ℤ, ∑ q : Fin (layerSlots (T + m)).length,
        scheduledReferenceRowTest d initial j
          (fun u => vacuumLeading a u j * f u) ⟨m, q⟩ := by
      apply Summable.tsum_finsetSum
      intro m _
      exact (hasSum_sum (fun q _ =>
        (scheduledReferenceRowTest_summable d initial f ⟨m, q⟩).hasSum)).summable
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Summable.tsum_finsetSum (fun q _ =>
        scheduledReferenceRowTest_summable d initial f ⟨m, q⟩)]
      exact Finset.sum_congr rfl (fun q _ => tsum_scheduledReferenceRowTest d initial f ⟨m, q⟩)

/-- Exact low-front boundary and finite actual-cell decomposition of the
integer-spin leading reference for a fixed-family datum. -/
theorem fixedFamily_integerLeadingTest_eq_boundary_add_cell
    {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ X : ℝ}
    (D : FixedFamilyDatum g a δ) (f : ℝ → ℝ) (hf : Continuous f)
    (hzero : ∀ u, X ≤ u → f u = 0) (k : ℕ) (hk : X ≤ ((g.start + k : ℕ) : ℝ)) :
    integerLeadingTest (shift (gapFamilyCharge a)) g.start f =
      frontBoundaryTest (shift (gapFamilyCharge a)) g.start D.initialState.front f +
      ∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (g.start + m)).length,
        scheduledLeadingCellTest D.tail D.initialState f ⟨m, q⟩ := by
  rw [fixedFamily_integerLeadingTest_eq_boundary_add_tail D f hf hzero]
  congr 1
  symm
  apply sum_scheduledLeadingCellTest_eq_tail D.tail D.initialState f hf hzero
    (by linarith [D.charge_large]) (by exact_mod_cast g.start_pos) D.initial_front k
  intro j
  exact hk.trans ((le_max_left _ _).trans ((D.state_spec k).2.2.2.1 j))

end BTZEntropy.Comparison
