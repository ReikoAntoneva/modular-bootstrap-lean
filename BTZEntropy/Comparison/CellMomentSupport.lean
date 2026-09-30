import BTZEntropy.Comparison.CellMomentRate

/-!
# Selecting the cell and descendant pairs that meet the test window

The scalar replacement error vanishes when the entire cell misses the
descendant-shifted kernel window. Finite comparisons can therefore discard
those pairs before estimating their mass. A retained cell lies in the same
window enlarged by its width, which is at most one.
-/

noncomputable section

open Set MeasureTheory GapFamily.Analytic GapFamily.Construction
open scoped BigOperators Classical

namespace BTZEntropy.Comparison

/-- Vanishing on the whole closed cell kills both its literal node test and
its actual density integral. No sign condition on the density is required. -/
theorem tailCellDescendantDifference_eq_zero_of_test_eq_zero
    {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ} (cell : TailCell j L k ρ)
    (φ : SmoothKernel) (q : ℕ) (E : ℝ)
    (hzero : ∀ u ∈ Icc L cell.right, descendantTest φ q E u = 0) :
    tailCellDescendantDifference cell φ q E = 0 := by
  have hn : (∑ i, descendantTest φ q E (cell.node i)) = 0 :=
    Finset.sum_eq_zero fun i _ => hzero _ (cell.node_mem i)
  have hi : (∫ u in Ioo L cell.right,
      ρ u * descendantTest φ q E u ∂referenceMeasure j) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    rw [hzero u ⟨hu.1.le, hu.2.le⟩, mul_zero]
  simp only [tailCellDescendantDifference, hn, hi, sub_self]

/-- A closed cell is relevant if it intersects the support window translated
by its particular descendant level. The definition is independent of nodes. -/
def tailCellDescendantRelevant
    {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ} (cell : TailCell j L k ρ)
    (q : ℕ) (E R : ℝ) : Prop :=
  L ≤ E + R + 1 / 12 - (q : ℝ) ∧
    E - R + 1 / 12 - (q : ℝ) ≤ cell.right

/-- Any nonzero test point forces this cell and descendant pair to be
relevant. The support assumption concerns the original prescribed kernel. -/
theorem tailCellDescendantRelevant_of_test_ne_zero
    {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ} (cell : TailCell j L k ρ)
    (φ : SmoothKernel) (q : ℕ) (E R : ℝ)
    (hR : ∀ v, φ v ≠ 0 → |v| ≤ R) {u : ℝ}
    (hu : u ∈ Icc L cell.right) (hφ : descendantTest φ q E u ≠ 0) :
    tailCellDescendantRelevant cell q E R := by
  have hb := abs_le.mp (hR _ hφ)
  dsimp [tailCellDescendantRelevant]
  constructor <;> linarith [hu.1, hu.2, hb.1, hb.2]

/-- Every omitted cell and descendant pair has zero test on the whole cell. -/
theorem descendantTest_eq_zero_of_not_relevant
    {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ} (cell : TailCell j L k ρ)
    (φ : SmoothKernel) (q : ℕ) (E R : ℝ)
    (hR : ∀ v, φ v ≠ 0 → |v| ≤ R)
    (hnot : ¬ tailCellDescendantRelevant cell q E R) :
    ∀ u ∈ Icc L cell.right, descendantTest φ q E u = 0 := by
  intro u hu
  by_contra hφ
  exact hnot (tailCellDescendantRelevant_of_test_ne_zero cell φ q E R hR hu hφ)

/-- The genuine replacement error is exactly zero outside the kernel window. -/
theorem tailCellDescendantDifference_eq_zero_of_not_relevant
    {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ} (cell : TailCell j L k ρ)
    (φ : SmoothKernel) (q : ℕ) (E R : ℝ)
    (hR : ∀ v, φ v ≠ 0 → |v| ≤ R)
    (hnot : ¬ tailCellDescendantRelevant cell q E R) :
    tailCellDescendantDifference cell φ q E = 0 :=
  tailCellDescendantDifference_eq_zero_of_test_eq_zero cell φ q E
    (descendantTest_eq_zero_of_not_relevant cell φ q E R hR hnot)

/-- Explicit strict separation of the cell from the translated support
window is enough for exact vanishing, including every unit node. -/
theorem tailCellDescendantDifference_eq_zero_of_outside
    {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ} (cell : TailCell j L k ρ)
    (φ : SmoothKernel) (q : ℕ) (E R : ℝ)
    (hR : ∀ v, φ v ≠ 0 → |v| ≤ R)
    (hout : cell.right < E - R + 1 / 12 - (q : ℝ) ∨
      E + R + 1 / 12 - (q : ℝ) < L) :
    tailCellDescendantDifference cell φ q E = 0 := by
  apply tailCellDescendantDifference_eq_zero_of_not_relevant cell φ q E R hR
  rintro ⟨hL, hV⟩
  rcases hout with h | h <;> linarith

/-- All points of a retained cell lie in the support window enlarged by one.
This allows mass estimates to be made after selecting cell and level pairs. -/
theorem tailCellDescendantRelevant_testArgument_le
    {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ} (cell : TailCell j L k ρ)
    (q : ℕ) (E R : ℝ) (hrel : tailCellDescendantRelevant cell q E R)
    {u : ℝ} (hu : u ∈ Icc L cell.right) :
    |u - 1 / 12 + (q : ℝ) - E| ≤ R + 1 := by
  rcases hrel with ⟨hL, hV⟩
  apply abs_le.mpr
  constructor <;> linarith [cell.right_mem.2, hu.1, hu.2]

/-- A finite rectangular sum equals a selected pair sum if all omitted
summands vanish. The selected pairs need not themselves form a rectangle. -/
theorem sum_pair_eq_selected {ι κ : Type*} (I : Finset ι) (F : Finset κ)
    (S : Finset (ι × κ)) (hS : S ⊆ I ×ˢ F) (f : ι → κ → ℝ)
    (hzero : ∀ i ∈ I, ∀ l ∈ F, (i, l) ∉ S → f i l = 0) :
    (∑ i ∈ I, ∑ l ∈ F, f i l) = ∑ p ∈ S, f p.1 p.2 := by
  rw [← Finset.sum_product I F (fun p : ι × κ => f p.1 p.2)]
  symm
  apply Finset.sum_subset hS
  intro p hp hpS
  have hmem := Finset.mem_product.mp hp
  exact hzero p.1 hmem.1 p.2 hmem.2 hpS

/-- Select genuine cell and descendant errors before using any mass bound.
Only the omitted pairs' full-cell vanishing is needed. -/
theorem finiteTailCell_descendantDifference_eq_selected
    {ι : Type*} (I : Finset ι) (j : ι → ℤ) (L : ι → ℝ) (k : ι → ℕ)
    (ρ : ι → ℝ → ℝ) (cell : ∀ i, TailCell (j i) (L i) (k i) (ρ i))
    (φ : SmoothKernel) (E : ℝ) (F : Finset (ℕ × ℕ))
    (S : Finset (ι × (ℕ × ℕ))) (hS : S ⊆ I ×ˢ F)
    (hzero : ∀ i ∈ I, ∀ l ∈ F, (i, l) ∉ S →
      ∀ u ∈ Icc (L i) (cell i).right, descendantTest φ (l.1 + l.2) E u = 0) :
    (∑ i ∈ I, ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
      tailCellDescendantDifference (cell i) φ (l.1 + l.2) E) =
      ∑ p ∈ S, (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
        tailCellDescendantDifference (cell p.1) φ (p.2.1 + p.2.2) E := by
  apply sum_pair_eq_selected I F S hS
  intro i hi l hl hnot
  rw [tailCellDescendantDifference_eq_zero_of_test_eq_zero (cell i) φ _ E
    (hzero i hi l hl hnot), mul_zero]

/-- The canonical selection keeps exactly the cell and level pairs whose
closed cell meets that level's translated support window. -/
theorem finiteTailCell_descendantDifference_eq_relevant
    {ι : Type*} (I : Finset ι) (j : ι → ℤ) (L : ι → ℝ) (k : ι → ℕ)
    (ρ : ι → ℝ → ℝ) (cell : ∀ i, TailCell (j i) (L i) (k i) (ρ i))
    (φ : SmoothKernel) (E R : ℝ) (F : Finset (ℕ × ℕ))
    (hR : ∀ v, φ v ≠ 0 → |v| ≤ R) :
    (∑ i ∈ I, ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
      tailCellDescendantDifference (cell i) φ (l.1 + l.2) E) =
      ∑ p ∈ (I ×ˢ F).filter
          (fun p => tailCellDescendantRelevant (cell p.1) (p.2.1 + p.2.2) E R),
        (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
          tailCellDescendantDifference (cell p.1) φ (p.2.1 + p.2.2) E := by
  apply finiteTailCell_descendantDifference_eq_selected I j L k ρ cell φ E F _
    (Finset.filter_subset _ _)
  intro i hi l hl hnot
  apply descendantTest_eq_zero_of_not_relevant (cell i) φ _ E R hR
  intro hrel
  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hl⟩, hrel⟩)

/-- Pair-dependent selection on the exact active cells of the real scheduler. -/
theorem activeSlot_descendantDifference_eq_relevant
    {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
    (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)
    (I : Finset (d.ActiveSlot initial))
    (φ : SmoothKernel) (E R : ℝ) (F : Finset (ℕ × ℕ))
    (hR : ∀ v, φ v ≠ 0 → |v| ≤ R) :
    (∑ i ∈ I, ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
      tailCellDescendantDifference (d.activeCell initial i) φ (l.1 + l.2) E) =
      ∑ p ∈ (I ×ˢ F).filter
          (fun p => tailCellDescendantRelevant (d.activeCell initial p.1)
            (p.2.1 + p.2.2) E R),
        (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
          tailCellDescendantDifference (d.activeCell initial p.1) φ (p.2.1 + p.2.2) E :=
  finiteTailCell_descendantDifference_eq_relevant I
    (fun i => i.val.row)
    (fun i => (d.slotPreState initial i.val).front i.val.row)
    (fun i => degree i.val.layer)
    (fun i => (d.slotPreState initial i.val).numerator i.val.row)
    (d.activeCell initial) φ E R F hR

/-- The actual emitted descendant packet minus its continuum packet is the
sum of the literal scalar replacement errors with their partition weights. -/
theorem tailCell_primaryDescendant_difference_eq
    {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ} (cell : TailCell j L k ρ)
    (φ : SmoothKernel) (E : ℝ) (F : Finset (ℕ × ℕ)) :
    (∑ n, primaryDescendantTest φ E F (cell.node n)) -
      (∫ u in Ioo L cell.right, ρ u * primaryDescendantTest φ E F u
        ∂referenceMeasure j) =
      ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
        tailCellDescendantDifference cell φ (l.1 + l.2) E := by
  rw [sum_primaryDescendantTest, tailCell_integral_primaryDescendantTest]
  simp only [tailCellDescendantDifference, mul_sub, Finset.sum_sub_distrib,
    descendantTest, Nat.cast_add, ← add_assoc]

/-- Pair selection holds directly for the scheduler's emitted packet minus
the sum of its true density integrals. This is the quantity entering the
permanent-spectrum comparison. -/
theorem activeSlot_primaryDescendant_difference_eq_relevant
    {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
    (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)
    (I : Finset (d.ActiveSlot initial))
    (φ : SmoothKernel) (E R : ℝ) (F : Finset (ℕ × ℕ))
    (hR : ∀ v, φ v ≠ 0 → |v| ≤ R) :
    (∑ i ∈ I, scheduledCellTest d initial
        (fun p => primaryDescendantTest φ E F p.1) i.val) -
      (∑ i ∈ I, ∫ u in Ioo ((d.slotPreState initial i.val).front i.val.row)
          (d.activeCell initial i).right,
        (d.slotPreState initial i.val).numerator i.val.row u *
          primaryDescendantTest φ E F u ∂referenceMeasure i.val.row) =
      ∑ p ∈ (I ×ˢ F).filter
          (fun p => tailCellDescendantRelevant (d.activeCell initial p.1)
            (p.2.1 + p.2.2) E R),
        (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
          tailCellDescendantDifference (d.activeCell initial p.1) φ (p.2.1 + p.2.2) E := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [scheduledCellTest_active, tailCell_primaryDescendant_difference_eq]
  exact activeSlot_descendantDifference_eq_relevant d initial I φ E R F hR

/-- The actual scheduled descendant packet has every inverse-charge error
bound with only the true absolute density mass on relevant cell and level
pairs remaining. No positivity, local approximation, or entropy hypothesis
is required. The constant depends solely on the kernel and requested order. -/
theorem exists_uniform_relevantPacket_absMass_error_le (φ : SmoothKernel) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a U : ℝ), 0 ≤ a → ∀ (T K : ℕ), 0 < K →
      ∀ (d : RealTailLocalData a U T (realTailMomentDegree K a))
        (initial : FiniteRepairState) (I : Finset (d.ActiveSlot initial))
        (E R : ℝ) (F : Finset (ℕ × ℕ)),
      (∀ v, φ v ≠ 0 → |v| ≤ R) →
      |(∑ i ∈ I, scheduledCellTest d initial
          (fun p => primaryDescendantTest φ E F p.1) i.val) -
        ∑ i ∈ I, ∫ u in Ioo ((d.slotPreState initial i.val).front i.val.row)
            (d.activeCell initial i).right,
          (d.slotPreState initial i.val).numerator i.val.row u *
            primaryDescendantTest φ E F u ∂referenceMeasure i.val.row| ≤
        C * (∑ p ∈ (I ×ˢ F).filter
            (fun p => tailCellDescendantRelevant (d.activeCell initial p.1)
              (p.2.1 + p.2.2) E R),
          (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
            tailCellAbsoluteMass (d.activeCell initial p.1)) / (1 + a) ^ P := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_selectedPair_absMass_error_le φ P
  refine ⟨C, hC, ?_⟩
  intro a U ha T K hK d initial I E R F hR
  rw [activeSlot_primaryDescendant_difference_eq_relevant d initial I φ E R F hR]
  simpa only [tailCellDescendantDifference, mul_sub, Finset.sum_sub_distrib] using
    hbound a U ha T K hK d initial
      ((I ×ˢ F).filter (fun p => tailCellDescendantRelevant (d.activeCell initial p.1)
        (p.2.1 + p.2.2) E R)) E

end BTZEntropy.Comparison
