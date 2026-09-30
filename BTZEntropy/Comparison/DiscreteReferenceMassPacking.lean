import BTZEntropy.Comparison.CellMomentSupport
import BTZEntropy.Comparison.CellMassEnvelope

/-!
# Packing actual cell masses into the integer-spin reference

Chronological disjointness lets every finite collection of actual cells use
each part of its row reference at most once. Descendant-dependent cutoffs are
retained when this bound is applied to the relevant cell and level pairs.
-/

noncomputable section

open Set MeasureTheory GapFamily.Analytic GapFamily.Construction
open scoped BigOperators Classical

namespace BTZEntropy.Comparison

/-- Finite disjoint row cells consume at most the mass of their common row
windows. Only cells in the selected finite set need lie in those windows. -/
theorem sum_integral_disjoint_row_windows_le {ι : Type*}
    (J : ι → ℤ) (s : ι → Set ℝ) (μ : ℤ → Measure ℝ)
    (f : ℤ → ℝ → ℝ) (W : ℤ → Set ℝ) (I : Finset ι)
    (hs : ∀ i, MeasurableSet (s i))
    (hdis : ∀ i k, i ≠ k → J i = J k → Disjoint (s i) (s k))
    (hsub : ∀ i ∈ I, s i ⊆ W (J i))
    (hf : ∀ j, IntegrableOn (f j) (W j) (μ j))
    (hnonneg : ∀ j, 0 ≤ᵐ[(μ j).restrict (W j)] f j)
    (hsum : Summable (fun j => ∫ x in W j, f j x ∂μ j)) :
    (∑ i ∈ I, ∫ x in s i, f (J i) x ∂μ (J i)) ≤
      ∑' j, ∫ x in W j, f j x ∂μ j := by
  have hfiber (j : ℤ) :
      ∑ i ∈ I with J i = j, ∫ x in s i, f j x ∂μ j ≤
        ∫ x in W j, f j x ∂μ j := by
    have hsub' : ∀ i ∈ I.filter (fun i => J i = j), s i ⊆ W j := by
      intro i hi
      have hm := Finset.mem_filter.mp hi
      simpa only [hm.2] using hsub i hm.1
    rw [← integral_biUnion_finset (I.filter (fun i => J i = j))
      (fun i _ => hs i) (by
        intro i hi k hk hik
        exact hdis i k hik
          ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm))
      (fun i hi => (hf j).mono_set (hsub' i hi))]
    apply setIntegral_mono_set (hf j) (hnonneg j)
    exact Filter.Eventually.of_forall fun x hx => by
      simp only [mem_iUnion] at hx
      obtain ⟨i, hi, hx⟩ := hx
      exact hsub' i hi hx
  calc
    _ = ∑ j ∈ I.image J, ∑ i ∈ I with J i = j,
          ∫ x in s i, f (J i) x ∂μ (J i) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem J hi)
        (fun i => ∫ x in s i, f (J i) x ∂μ (J i))).symm
    _ = ∑ j ∈ I.image J, ∑ i ∈ I with J i = j,
          ∫ x in s i, f j x ∂μ j := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ j ∈ I.image J, ∫ x in W j, f j x ∂μ j :=
      Finset.sum_le_sum (fun j _ => hfiber j)
    _ ≤ _ := hsum.sum_le_tsum (I.image J)
      (fun j _ => integral_nonneg_of_ae (hnonneg j))

/-- The actual scheduled intervals fit their common finite-energy physical
window whenever their right endpoints do. -/
theorem activeCell_interval_subset_window {a U X : ℝ} {T : ℕ}
    {degree : ℕ → ℕ} (d : RealTailLocalData a U T degree)
    (initial : FiniteRepairState) (i : d.ActiveSlot initial)
    (hX : (d.activeCell initial i).right ≤ X) :
    Ioo ((d.slotPreState initial i.val).front i.val.row)
        (d.activeCell initial i).right ⊆ Ioo (max (T : ℝ) |(i.val.row : ℝ)|) X := by
  intro E hE
  exact ⟨lt_of_le_of_lt (max_le (d.activeCell_front_lower initial i)
    i.property.physical) hE.1, hE.2.trans_le hX⟩

/-- A finite-energy envelope bound for literal active cells. The local
envelope is already part of actual slot validity, including signed spin-edge
cells; no density positivity or extra initial-state condition is assumed. -/
theorem sum_activeCell_absoluteMass_le_row_integral
    {a U X : ℝ} {T : ℕ} {degree : ℕ → ℕ}
    (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)
    (I : Finset (d.ActiveSlot initial)) (ha : 2 ≤ a) (hT : (1 : ℝ) ≤ T)
    (hX : ∀ i ∈ I, (d.activeCell initial i).right ≤ X)
    (hf : ∀ j : ℤ, IntegrableOn (fun E => tailEnvelopeNumerator a E j)
      (Ioo (max (T : ℝ) |(j : ℝ)|) X) (referenceMeasure j))
    (hsum : Summable (fun j : ℤ => ∫ E in Ioo (max (T : ℝ) |(j : ℝ)|) X,
      tailEnvelopeNumerator a E j ∂referenceMeasure j)) :
    (∑ i ∈ I, tailCellAbsoluteMass (d.activeCell initial i)) ≤
      ∑' j : ℤ, ∫ E in Ioo (max (T : ℝ) |(j : ℝ)|) X,
        tailEnvelopeNumerator a E j ∂referenceMeasure j := by
  calc
    _ ≤ ∑ i ∈ I, ∫ E in
        Ioo ((d.slotPreState initial i.val).front i.val.row)
          (d.activeCell initial i).right,
        tailEnvelopeNumerator a E i.val.row ∂referenceMeasure i.val.row := by
      apply Finset.sum_le_sum
      intro i _
      exact tailCellAbsoluteMass_le_tailEnvelope (d.activeCell initial i) ha
        (hT.trans (d.activeCell_front_lower initial i))
        i.property.physical i.property.envelope
    _ ≤ _ := sum_integral_disjoint_row_windows_le
      (fun i : d.ActiveSlot initial => i.val.row)
      (fun i => Ioo ((d.slotPreState initial i.val).front i.val.row)
        (d.activeCell initial i).right)
      referenceMeasure (fun j E => tailEnvelopeNumerator a E j)
      (fun j => Ioo (max (T : ℝ) |(j : ℝ)|) X) I
      (fun _ => measurableSet_Ioo) (d.activeCell_pairwise_disjoint initial)
      (fun i hi => activeCell_interval_subset_window d initial i (hX i hi)) hf
      (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
        exact tailEnvelopeNumerator_nonneg a E j ha
          ((le_max_right _ _).trans hE.1.le)) hsum

/-- The complete finite-energy envelope bounds every selected finite set of
literal active cells, with no dependence on the number of selected cells. -/
theorem sum_activeCell_absoluteMass_le_cellEnvelopeMass
    {a U X : ℝ} {T : ℕ} {degree : ℕ → ℕ}
    (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)
    (I : Finset (d.ActiveSlot initial)) (ha : 100 ≤ a) (hT : (1 : ℝ) ≤ T)
    (hX : ∀ i ∈ I, (d.activeCell initial i).right ≤ X) :
    (∑ i ∈ I, tailCellAbsoluteMass (d.activeCell initial i)) ≤
      cellEnvelopeMass a T X := by
  exact sum_activeCell_absoluteMass_le_row_integral d initial I (by linarith) hT hX
    (fun j => integrable_cellEnvelopeRow j hT) (cellEnvelopeRowMass_summable a T X)

/-- Grouping by the actual descendant pair preserves its own remaining
energy cutoff. The two partition multiplicities are retained exactly. -/
theorem sum_selectedPair_absoluteMass_le_cellEnvelopeMass
    {a U X : ℝ} {T : ℕ} {degree : ℕ → ℕ}
    (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)
    (S : Finset (d.ActiveSlot initial × (ℕ × ℕ))) (F : Finset (ℕ × ℕ))
    (ha : 100 ≤ a) (hT : (1 : ℝ) ≤ T)
    (hF : ∀ p ∈ S, p.2 ∈ F)
    (hX : ∀ p ∈ S, (d.activeCell initial p.1).right ≤
      X - ((p.2.1 + p.2.2 : ℕ) : ℝ)) :
    (∑ p ∈ S, (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
      tailCellAbsoluteMass (d.activeCell initial p.1)) ≤
      ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
        cellEnvelopeMass a T (X - ((l.1 + l.2 : ℕ) : ℝ)) := by
  have hfiber (l : ℕ × ℕ) :
      (∑ p ∈ S with p.2 = l, tailCellAbsoluteMass (d.activeCell initial p.1)) ≤
        cellEnvelopeMass a T (X - ((l.1 + l.2 : ℕ) : ℝ)) := by
    let I := (S.filter (fun p => p.2 = l)).image Prod.fst
    have hsum : (∑ i ∈ I, tailCellAbsoluteMass (d.activeCell initial i)) =
        ∑ p ∈ S with p.2 = l, tailCellAbsoluteMass (d.activeCell initial p.1) := by
      apply Finset.sum_image
      intro p hp q hq hpq
      exact Prod.ext hpq ((Finset.mem_filter.mp hp).2.trans
        (Finset.mem_filter.mp hq).2.symm)
    rw [← hsum]
    apply sum_activeCell_absoluteMass_le_cellEnvelopeMass d initial I ha hT
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    have hm := Finset.mem_filter.mp hp
    simpa only [hm.2] using hX p hm.1
  calc
    _ = ∑ l ∈ F, ∑ p ∈ S with p.2 = l,
        (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
          tailCellAbsoluteMass (d.activeCell initial p.1) :=
      (Finset.sum_fiberwise_of_maps_to hF _).symm
    _ = ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
        ∑ p ∈ S with p.2 = l, tailCellAbsoluteMass (d.activeCell initial p.1) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ ≤ _ := Finset.sum_le_sum fun l _ =>
      mul_le_mul_of_nonneg_left (hfiber l) (by positivity)

/-- Every relevant cell is contained below the test window enlarged by its
width. This is the same finite shift for all rows and descendant levels. -/
theorem tailCellDescendantRelevant_right_le
    {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ} (cell : TailCell j L k ρ)
    {q : ℕ} {E R : ℝ} (hrel : tailCellDescendantRelevant cell q E R) :
    cell.right ≤ E + R + 13 / 12 - (q : ℝ) := by
  linarith [hrel.1, cell.right_mem.2]

/-- The canonical relevant cell and descendant pairs fit the finite-energy
envelope with their full descendant-dependent cutoff and exact weights. -/
theorem sum_relevantPair_absoluteMass_le_cellEnvelopeMass
    {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
    (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)
    (I : Finset (d.ActiveSlot initial)) (F : Finset (ℕ × ℕ))
    (E R : ℝ) (ha : 100 ≤ a) (hT : (1 : ℝ) ≤ T) :
    (∑ p ∈ (I ×ˢ F).filter
        (fun p => tailCellDescendantRelevant (d.activeCell initial p.1)
          (p.2.1 + p.2.2) E R),
      (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
        tailCellAbsoluteMass (d.activeCell initial p.1)) ≤
      ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
        cellEnvelopeMass a T (E + R + 13 / 12 - ((l.1 + l.2 : ℕ) : ℝ)) := by
  apply sum_selectedPair_absoluteMass_le_cellEnvelopeMass d initial _ F ha hT
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp
    exact tailCellDescendantRelevant_right_le (d.activeCell initial p.1)
      (Finset.mem_filter.mp hp).2

end BTZEntropy.Comparison
