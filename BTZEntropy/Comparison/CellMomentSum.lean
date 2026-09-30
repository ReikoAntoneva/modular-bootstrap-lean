import BTZEntropy.Comparison.MomentTest
import BTZEntropy.Comparison.MomentSum
import BTZEntropy.Comparison.SpectrumTestSmooth

/-!
# Summing genuine cell comparisons

Descendant multiplicities are their actual partition weights. The comparison
uses each cell's literal nodes and density integral, including the cells at
the preceding states of the real scheduler. Once scalar local estimates are
known, the only remaining bound is on the displayed weighted node count.
-/

noncomputable section

open Set MeasureTheory GapFamily GapFamily.Analytic GapFamily.Construction
open scoped BigOperators Classical

namespace BTZEntropy.Comparison

/-- Expand the actual continuum test into its finite descendant packet.
Integrability follows from the cell's integrable density and continuity of
the prescribed smooth kernel. -/
theorem tailCell_integral_primaryDescendantTest
    {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ} (cell : TailCell j L k ρ)
    (φ : SmoothKernel) (E : ℝ) (F : Finset (ℕ × ℕ)) :
    (∫ u in Ioo L cell.right, ρ u * primaryDescendantTest φ E F u
      ∂referenceMeasure j) =
      ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
        ∫ u in Ioo L cell.right, ρ u * descendantTest φ (l.1 + l.2) E u
          ∂referenceMeasure j := by
  have hi (l : ℕ × ℕ) : IntegrableOn
      (fun u => ρ u * descendantTest φ (l.1 + l.2) E u)
      (Ioo L cell.right) (referenceMeasure j) :=
    (cellResidualMeasure_integral_continuous j L cell.right cell.node
      cell.density_integrable (continuous_descendantTest φ _ E)).2.1
  have hfun (u : ℝ) : ρ u * primaryDescendantTest φ E F u =
      ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
        (ρ u * descendantTest φ (l.1 + l.2) E u) := by
    simp only [primaryDescendantTest, Finset.mul_sum, descendantTest, Nat.cast_add,
      ← add_assoc]
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hfun]
  rw [integral_finsetSum F (fun l _ => (hi l).const_mul _)]
  apply Finset.sum_congr rfl
  intro l _
  exact integral_const_mul _ _

/-- A cell's complete finite descendant packet inherits its scalar local
error bound with the exact sum of partition-weighted unit-node counts. -/
theorem tailCell_primaryDescendant_error_le
    {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ} (cell : TailCell j L k ρ)
    (φ : SmoothKernel) (E : ℝ) (F : Finset (ℕ × ℕ)) (ε : ℝ)
    (hlocal : ∀ l ∈ F,
      |(∑ n, descendantTest φ (l.1 + l.2) E (cell.node n)) -
        ∫ u in Ioo L cell.right, ρ u * descendantTest φ (l.1 + l.2) E u
          ∂referenceMeasure j| ≤ (cell.count : ℝ) * ε) :
    |(∑ n, primaryDescendantTest φ E F (cell.node n)) -
      ∫ u in Ioo L cell.right, ρ u * primaryDescendantTest φ E F u
        ∂referenceMeasure j| ≤
      (∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) * cell.count) * ε := by
  rw [tailCell_integral_primaryDescendantTest, sum_primaryDescendantTest]
  have h := abs_weighted_sum_sub_le F
    (fun l => (partitionCount l.1 * partitionCount l.2 : ℝ))
    (fun _ => (cell.count : ℝ))
    (fun l => ∑ n, descendantTest φ (l.1 + l.2) E (cell.node n))
    (fun l => ∫ u in Ioo L cell.right,
      ρ u * descendantTest φ (l.1 + l.2) E u ∂referenceMeasure j) ε
    (fun l _ => by positivity) hlocal
  simpa only [descendantTest, Nat.cast_add, ← add_assoc] using h

/-- Sum actual cells and descendant packets. The remaining mass is the
literal finite sum of partition-weighted counts, not an abstract majorant. -/
theorem finiteTailCell_primaryDescendant_error_le
    {ι : Type*} (I : Finset ι) (j : ι → ℤ) (L : ι → ℝ) (k : ι → ℕ)
    (ρ : ι → ℝ → ℝ) (cell : ∀ i, TailCell (j i) (L i) (k i) (ρ i))
    (φ : SmoothKernel) (E : ℝ) (F : Finset (ℕ × ℕ)) (ε : ℝ)
    (hlocal : ∀ i ∈ I, ∀ l ∈ F,
      |(∑ n, descendantTest φ (l.1 + l.2) E ((cell i).node n)) -
        ∫ u in Ioo (L i) (cell i).right,
          ρ i u * descendantTest φ (l.1 + l.2) E u ∂referenceMeasure (j i)| ≤
            ((cell i).count : ℝ) * ε) :
    |(∑ i ∈ I, ∑ n, primaryDescendantTest φ E F ((cell i).node n)) -
      ∑ i ∈ I, ∫ u in Ioo (L i) (cell i).right,
        ρ i u * primaryDescendantTest φ E F u ∂referenceMeasure (j i)| ≤
      (∑ i ∈ I, ∑ l ∈ F,
        (partitionCount l.1 * partitionCount l.2 : ℝ) * (cell i).count) * ε := by
  have h := abs_weighted_sum_sub_le I (fun _ => (1 : ℝ))
    (fun i => ∑ l ∈ F,
      (partitionCount l.1 * partitionCount l.2 : ℝ) * (cell i).count)
    (fun i => ∑ n, primaryDescendantTest φ E F ((cell i).node n))
    (fun i => ∫ u in Ioo (L i) (cell i).right,
      ρ i u * primaryDescendantTest φ E F u ∂referenceMeasure (j i)) ε
    (fun _ _ => zero_le_one)
    (fun i hi => tailCell_primaryDescendant_error_le (cell i) φ E F ε (hlocal i hi))
  simpa only [one_mul] using h

/-- The same estimate applies to the scheduler's actual cells at their
literal preceding states and to its actual emitted descendant tests. -/
theorem activeSlot_primaryDescendant_error_le
    {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
    (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)
    (I : Finset (d.ActiveSlot initial))
    (φ : SmoothKernel) (E : ℝ) (F : Finset (ℕ × ℕ)) (ε : ℝ)
    (hlocal : ∀ i ∈ I, ∀ l ∈ F,
      |(∑ n, descendantTest φ (l.1 + l.2) E ((d.activeCell initial i).node n)) -
        ∫ u in Ioo ((d.slotPreState initial i.val).front i.val.row)
            (d.activeCell initial i).right,
          (d.slotPreState initial i.val).numerator i.val.row u *
            descendantTest φ (l.1 + l.2) E u ∂referenceMeasure i.val.row| ≤
              ((d.activeCell initial i).count : ℝ) * ε) :
    |(∑ i ∈ I, scheduledCellTest d initial
        (fun p => primaryDescendantTest φ E F p.1) i.val) -
      ∑ i ∈ I, ∫ u in Ioo ((d.slotPreState initial i.val).front i.val.row)
          (d.activeCell initial i).right,
        (d.slotPreState initial i.val).numerator i.val.row u *
          primaryDescendantTest φ E F u ∂referenceMeasure i.val.row| ≤
      (∑ i ∈ I, ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
        (d.activeCell initial i).count) * ε := by
  simp_rw [scheduledCellTest_active]
  exact finiteTailCell_primaryDescendant_error_le I
    (fun i => i.val.row)
    (fun i => (d.slotPreState initial i.val).front i.val.row)
    (fun i => degree i.val.layer)
    (fun i => (d.slotPreState initial i.val).numerator i.val.row)
    (d.activeCell initial) φ E F ε hlocal

end BTZEntropy.Comparison
