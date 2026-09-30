import BTZEntropy.Comparison.CellMassDescendant
import BTZEntropy.Comparison.DiscreteReferenceMassPacking

/-!
# The actual replacement error at the leading exponential scale

Disjoint actual cells, the descendant-dependent support window, and the
convergent partition-weighted envelope turn local moment cancellation into
a uniform complete finite-packet estimate. The recursion and its node choices
remain arbitrary; only their genuine moment-degree lower bound is needed.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic GapFamily.Construction
open scoped BigOperators Classical

namespace BTZEntropy.Comparison

/-- Actual relevant-pair absolute masses have the unchanged leading
exponential rate. The constant includes every descendant level and does not
grow with either finite construction cutoff. -/
theorem sum_relevantPair_absoluteMass_le_exp
    {a U V : ℝ} {T : ℕ} {degree : ℕ → ℕ}
    (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)
    (I : Finset (d.ActiveSlot initial)) (F : Finset (ℕ × ℕ)) (E R : ℝ)
    (ha : 100 ≤ a) (hT : (1 : ℝ) ≤ T)
    (hX : 0 < E + R + 13 / 12) (hV : 0 < V)
    (hXV : E + R + 13 / 12 ≤ V * a) :
    (∑ p ∈ (I ×ˢ F).filter
        (fun p => tailCellDescendantRelevant (d.activeCell initial p.1)
          (p.2.1 + p.2.2) E R),
      (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
        tailCellAbsoluteMass (d.activeCell initial p.1)) ≤
      9 * (1 + (E + R + 13 / 12)) ^ 2 *
        exp (4 * π * sqrt (a * (E + R + 13 / 12))) *
          exp (4 / (2 * π / sqrt V)) := by
  apply (sum_relevantPair_absoluteMass_le_cellEnvelopeMass
    d initial I F E R ha hT).trans
  simpa only [Nat.cast_add] using
    cellEnvelopeMass_descendant_finset_le_exp ha hT hX hV hXV F

/-- The genuine selected-pair moment bound for an arbitrary retained degree
schedule. This avoids changing the dependent type of the actual selected
cells when a construction exposes its schedule by a proved equality. -/
theorem exists_uniform_relevantPacket_absMass_error_le_of_degree
    (φ : SmoothKernel) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a U : ℝ), 0 ≤ a →
      ∀ (T : ℕ) (degree : ℕ → ℕ) (d : RealTailLocalData a U T degree),
      (∀ m, a ≤ (degree m : ℝ)) →
      ∀ (initial : FiniteRepairState) (I : Finset (d.ActiveSlot initial))
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
  obtain ⟨C, hC, hlocal⟩ := exists_uniform_tailCell_absMass_error_le φ P
  refine ⟨C, hC, ?_⟩
  intro a U ha T degree d hdegree initial I E R F hR
  rw [activeSlot_primaryDescendant_difference_eq_relevant d initial I φ E R F hR]
  have hb := abs_weighted_sum_le
    ((I ×ˢ F).filter (fun p => tailCellDescendantRelevant
      (d.activeCell initial p.1) (p.2.1 + p.2.2) E R))
    (fun p => (partitionCount p.2.1 * partitionCount p.2.2 : ℝ))
    (fun p => tailCellAbsoluteMass (d.activeCell initial p.1))
    (fun p => tailCellDescendantDifference (d.activeCell initial p.1) φ
      (p.2.1 + p.2.2) E)
    (C / (1 + a) ^ P) (fun p _ => by positivity) (fun p _ => ?_)
  · convert hb using 1 <;> ring
  · have hb := hlocal a ha p.1.val.row _ _ _ (d.activeCell initial p.1)
      p.1.property.physical (hdegree _) (p.2.1 + p.2.2) E
    convert hb using 1 <;> ring

/-- The final finite-packet replacement bound has no residual mass,
positivity, approximation, or local error premise. The constant depends only
on the prescribed kernel, the requested order, and a fixed upper energy to
charge ratio. Both infinite descendant towers have already been bounded. -/
theorem exists_uniform_relevantPacket_exp_error_le
    (φ : SmoothKernel) (P : ℕ) (V : ℝ) (hV : 0 < V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a U : ℝ), 100 ≤ a →
      ∀ (T : ℕ) (degree : ℕ → ℕ) (d : RealTailLocalData a U T degree),
      (1 : ℝ) ≤ T → (∀ m, a ≤ (degree m : ℝ)) →
      ∀ (initial : FiniteRepairState) (I : Finset (d.ActiveSlot initial))
        (E R : ℝ) (F : Finset (ℕ × ℕ)),
      (∀ v, φ v ≠ 0 → |v| ≤ R) → 0 < E + R + 13 / 12 →
      E + R + 13 / 12 ≤ V * a →
      |(∑ i ∈ I, scheduledCellTest d initial
          (fun p => primaryDescendantTest φ E F p.1) i.val) -
        ∑ i ∈ I, ∫ u in Ioo ((d.slotPreState initial i.val).front i.val.row)
            (d.activeCell initial i).right,
          (d.slotPreState initial i.val).numerator i.val.row u *
            primaryDescendantTest φ E F u ∂referenceMeasure i.val.row| ≤
        C * (1 + (E + R + 13 / 12)) ^ 2 *
          exp (4 * π * sqrt (a * (E + R + 13 / 12))) / (1 + a) ^ P := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_relevantPacket_absMass_error_le_of_degree φ P
  refine ⟨9 * C * exp (4 / (2 * π / sqrt V)), by positivity, ?_⟩
  intro a U ha T degree d hT hdegree initial I E R F hR hX hXV
  have hmass := sum_relevantPair_absoluteMass_le_exp d initial I F E R ha hT hX hV hXV
  apply (hbound a U (by linarith) T degree d hdegree initial I E R F hR).trans
  have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hC)
    (show 0 ≤ (1 + a) ^ P by positivity)
  convert hb using 1 <;> ring

end BTZEntropy.Comparison
