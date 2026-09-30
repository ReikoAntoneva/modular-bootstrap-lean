import BTZEntropy.Comparison.CellPolynomialApproximation
import BTZEntropy.Comparison.CellMomentSum
import GapFamily.Construction.RealTailMomentSchedule
import GapFamily.Construction.RealTailCellThermal

/-!
# Uniform inverse-charge error on the actual tail cells

Smooth polynomial approximation and the exact unit-node moments give every
inverse-power accuracy. The same constant works for all descendant levels,
observation energies, spins, node selectors, and cells. Positivity of the
current density is used only to identify its variation with its actual mass.
-/

noncomputable section

open Set MeasureTheory
open GapFamily.Analytic GapFamily.Construction
open scoped BigOperators

namespace BTZEntropy.Comparison

/-- The actual replacement error for one descendant level, including its
precise cylinder-energy shift. -/
def tailCellDescendantDifference {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ}
    (cell : TailCell j L k ρ) (φ : SmoothKernel) (q : ℕ) (E : ℝ) : ℝ :=
  (∑ i, descendantTest φ q E (cell.node i)) -
    ∫ u in Ioo L cell.right, ρ u * descendantTest φ q E u ∂referenceMeasure j

/-- The actual ordinary absolute mass of the current continuum being
replaced, valid also at a spin opening where the density may be signed. -/
def tailCellAbsoluteMass {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ}
    (cell : TailCell j L k ρ) : ℝ :=
  ∫ u in Ioo L cell.right, |ρ u| ∂referenceMeasure j

theorem tailCellAbsoluteMass_nonneg {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ}
    (cell : TailCell j L k ρ) : 0 ≤ tailCellAbsoluteMass cell :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem tailCell_count_le_absoluteMass {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ}
    (cell : TailCell j L k ρ) : (cell.count : ℝ) ≤ tailCellAbsoluteMass cell := by
  rw [← cell.mass_eq]
  exact integral_mono cell.density_integrable cell.density_integrable.abs
    (fun _ => le_abs_self _)

/-- The remaining absolute mass is bounded by the existing leading density
plus its genuine construction error envelope on the same cell. -/
theorem tailCellAbsoluteMass_le_tailEnvelope {a L : ℝ} {j : ℤ} {k : ℕ}
    {ρ : ℝ → ℝ} (cell : TailCell j L k ρ) (ha : 2 ≤ a) (hL : 1 ≤ L)
    (hj : |(j : ℝ)| ≤ L)
    (herror : ∀ u ∈ Icc L (L + 1),
      |ρ u - vacuumLeading a u j| ≤ Real.exp (7 * Real.sqrt (a * u))) :
    tailCellAbsoluteMass cell ≤
      ∫ u in Ioo L cell.right, tailEnvelopeNumerator a u j ∂referenceMeasure j := by
  exact setIntegral_mono_on cell.density_integrable.abs
    (integrableOn_tailEnvelopeNumerator a j hL hj (by linarith [cell.right_mem.1]))
    measurableSet_Ioo (cell.abs_le_tailEnvelope ha hj herror)

/-- A degree above the charge gives an inverse-charge bound with no hidden
large-charge threshold or degree-dependent constant. -/
theorem inverse_degree_pow_le_inverse_charge_pow {a C : ℝ} {k P : ℕ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hak : a ≤ (k : ℝ)) :
    C / ((k : ℝ) + 1) ^ P ≤ C / (1 + a) ^ P := by
  apply div_le_div_of_nonneg_left hC (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by linarith) P

/-- The literal scheduled moment degree dominates the real charge. -/
theorem realTailMomentDegree_ge_charge {K : ℕ} (hK : 0 < K) (a : ℝ) (m : ℕ) :
    a ≤ (realTailMomentDegree K a m : ℝ) := by
  rw [realTailMomentDegree_cast]
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hbase : a ≤ (⌈a⌉₊ : ℝ) + m + 1 := by
    linarith [Nat.le_ceil a, Nat.cast_nonneg (α := ℝ) m]
  exact hbase.trans (le_mul_of_one_le_left (by positivity) hK')

/-- The mass-and-variation form of the local error has a uniform inverse
degree constant, derived from the smooth kernel alone. This version does not
assume positivity of the density. -/
theorem exists_uniform_tailCell_variation_error_le (φ : SmoothKernel) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ), 0 ≤ a →
      ∀ (j : ℤ) (L : ℝ) (k : ℕ) (ρ : ℝ → ℝ) (cell : TailCell j L k ρ),
      |(j : ℝ)| ≤ L → a ≤ (k : ℝ) → ∀ (q : ℕ) (E : ℝ),
      |tailCellDescendantDifference cell φ q E| ≤
        C * ((cell.count : ℝ) +
          ∫ u in Ioo L cell.right, |ρ u| ∂referenceMeasure j) / (1 + a) ^ P := by
  obtain ⟨C, hC, hpoly⟩ := exists_uniform_cellTest_polynomial_approximation φ P
  refine ⟨C, hC, ?_⟩
  intro a ha j L k ρ cell hL hak q E
  obtain ⟨p, hp, happ⟩ := hpoly |(j : ℝ)| L cell.right
    (-1 / 12 + (q : ℝ) - E) hL (by linarith [cell.right_mem.1])
    (by linarith [cell.right_mem.2]) k
  have happ' : ∀ z ∈ Icc (0 : ℝ) 1,
      |descendantTest φ q E (normalizedCellEnergy |(j : ℝ)| L cell.right z) -
        p.eval z| ≤ C / ((k : ℝ) + 1) ^ P := by
    intro z hz
    convert happ z hz using 1
    congr 2
    unfold descendantTest
    congr 1
    ring
  have hb := tailCell_descendant_error_le cell hL φ q E p
    (Polynomial.natDegree_le_of_degree_le hp) (show 0 ≤ C / ((k : ℝ) + 1) ^ P by positivity)
    happ'
  change |tailCellDescendantDifference cell φ q E| ≤ _ at hb
  calc
    _ ≤ ((cell.count : ℝ) + ∫ u in Ioo L cell.right, |ρ u| ∂referenceMeasure j) *
        (C / ((k : ℝ) + 1) ^ P) := hb
    _ ≤ ((cell.count : ℝ) + ∫ u in Ioo L cell.right, |ρ u| ∂referenceMeasure j) *
        (C / (1 + a) ^ P) :=
      mul_le_mul_of_nonneg_left (inverse_degree_pow_le_inverse_charge_pow ha hC hak)
        (add_nonneg (Nat.cast_nonneg _) (integral_nonneg (fun _ => abs_nonneg _)))
    _ = _ := by ring

/-- The full all-order local estimate on positive current cells. Its constant
is independent of every spectrum and construction choice. -/
theorem exists_uniform_tailCell_error_le (φ : SmoothKernel) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ), 0 ≤ a →
      ∀ (j : ℤ) (L : ℝ) (k : ℕ) (ρ : ℝ → ℝ) (cell : TailCell j L k ρ),
      |(j : ℝ)| ≤ L → a ≤ (k : ℝ) →
      (∀ᵐ u ∂(referenceMeasure j).restrict (Ioo L cell.right), 0 ≤ ρ u) →
      ∀ (q : ℕ) (E : ℝ),
      |tailCellDescendantDifference cell φ q E| ≤
        C * (cell.count : ℝ) / (1 + a) ^ P := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_tailCell_variation_error_le φ P
  refine ⟨2 * C, by positivity, ?_⟩
  intro a ha j L k ρ cell hL hak hρ q E
  have habs : (∫ u in Ioo L cell.right, |ρ u| ∂referenceMeasure j) =
      (cell.count : ℝ) := by
    rw [← cell.mass_eq]
    exact integral_congr_ae (hρ.mono fun u hu => abs_of_nonneg hu)
  have hb := hbound a ha j L k ρ cell hL hak q E
  rw [habs] at hb
  convert hb using 1 <;> ring

/-- The count is at most the ordinary absolute mass, so the whole local
error is controlled by that single genuine mass without any positivity
assumption on the current density. -/
theorem exists_uniform_tailCell_absMass_error_le (φ : SmoothKernel) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ), 0 ≤ a →
      ∀ (j : ℤ) (L : ℝ) (k : ℕ) (ρ : ℝ → ℝ) (cell : TailCell j L k ρ),
      |(j : ℝ)| ≤ L → a ≤ (k : ℝ) → ∀ (q : ℕ) (E : ℝ),
      |tailCellDescendantDifference cell φ q E| ≤
        C * tailCellAbsoluteMass cell / (1 + a) ^ P := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_tailCell_variation_error_le φ P
  refine ⟨2 * C, by positivity, ?_⟩
  intro a ha j L k ρ cell hL hak q E
  have hb := hbound a ha j L k ρ cell hL hak q E
  change |tailCellDescendantDifference cell φ q E| ≤
    C * ((cell.count : ℝ) + tailCellAbsoluteMass cell) / (1 + a) ^ P at hb
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hm := mul_le_mul_of_nonneg_left
    (tailCell_count_le_absoluteMass cell) hC
  nlinarith

/-- The same theorem for the concrete moment schedule, without a separate
degree lower-bound premise. -/
theorem exists_uniform_scheduledTailCell_error_le (φ : SmoothKernel) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ), 0 ≤ a → ∀ (K : ℕ), 0 < K →
      ∀ (j : ℤ) (L : ℝ) (m : ℕ) (ρ : ℝ → ℝ)
        (cell : TailCell j L (realTailMomentDegree K a m) ρ),
      |(j : ℝ)| ≤ L →
      (∀ᵐ u ∂(referenceMeasure j).restrict (Ioo L cell.right), 0 ≤ ρ u) →
      ∀ (q : ℕ) (E : ℝ),
      |tailCellDescendantDifference cell φ q E| ≤
        C * (cell.count : ℝ) / (1 + a) ^ P := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_tailCell_error_le φ P
  exact ⟨C, hC, fun a ha K hK j L m ρ cell hL hρ q E =>
    hbound a ha j L _ ρ cell hL (realTailMomentDegree_ge_charge hK a m) hρ q E⟩

/-- Specialization to the exact cell selected in the actual preceding state
of the real-charge recursion. Only positivity of that current density remains. -/
theorem exists_uniform_activeCell_error_le (φ : SmoothKernel) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a U : ℝ), 0 ≤ a → ∀ (T K : ℕ), 0 < K →
      ∀ (d : RealTailLocalData a U T (realTailMomentDegree K a))
        (initial : FiniteRepairState) (p : d.ActiveSlot initial),
      (∀ᵐ u ∂(referenceMeasure p.val.row).restrict
        (Ioo ((d.slotPreState initial p.val).front p.val.row)
          (d.activeCell initial p).right),
        0 ≤ (d.slotPreState initial p.val).numerator p.val.row u) →
      ∀ (q : ℕ) (E : ℝ),
      |tailCellDescendantDifference (d.activeCell initial p) φ q E| ≤
        C * ((d.activeCell initial p).count : ℝ) / (1 + a) ^ P := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_scheduledTailCell_error_le φ P
  exact ⟨C, hC, fun a U ha T K hK d initial p hρ q E =>
    hbound a ha K hK p.val.row _ p.val.layer _ (d.activeCell initial p)
      p.property.physical hρ q E⟩

/-- Summing the same actual positive cells and their complete finite
descendant packets preserves every inverse-charge power. The only remaining
quantity is their explicit partition-weighted count, ready for the separate
reference-mass estimate. There is no local approximation premise left. -/
theorem exists_uniform_activePacket_error_le (φ : SmoothKernel) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a U : ℝ), 0 ≤ a → ∀ (T K : ℕ), 0 < K →
      ∀ (d : RealTailLocalData a U T (realTailMomentDegree K a))
        (initial : FiniteRepairState) (I : Finset (d.ActiveSlot initial)),
      (∀ i ∈ I, ∀ᵐ u ∂(referenceMeasure i.val.row).restrict
        (Ioo ((d.slotPreState initial i.val).front i.val.row)
          (d.activeCell initial i).right),
        0 ≤ (d.slotPreState initial i.val).numerator i.val.row u) →
      ∀ (E : ℝ) (F : Finset (ℕ × ℕ)),
      |(∑ i ∈ I, scheduledCellTest d initial
          (fun p => primaryDescendantTest φ E F p.1) i.val) -
        ∑ i ∈ I, ∫ u in Ioo ((d.slotPreState initial i.val).front i.val.row)
            (d.activeCell initial i).right,
          (d.slotPreState initial i.val).numerator i.val.row u *
            primaryDescendantTest φ E F u ∂referenceMeasure i.val.row| ≤
        C * (∑ i ∈ I, ∑ l ∈ F,
          (partitionCount l.1 * partitionCount l.2 : ℝ) *
            (d.activeCell initial i).count) / (1 + a) ^ P := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_activeCell_error_le φ P
  refine ⟨C, hC, ?_⟩
  intro a U ha T K hK d initial I hρ E F
  have hlocal : ∀ i ∈ I, ∀ l ∈ F,
      |(∑ n, descendantTest φ (l.1 + l.2) E ((d.activeCell initial i).node n)) -
        ∫ u in Ioo ((d.slotPreState initial i.val).front i.val.row)
            (d.activeCell initial i).right,
          (d.slotPreState initial i.val).numerator i.val.row u *
            descendantTest φ (l.1 + l.2) E u ∂referenceMeasure i.val.row| ≤
        ((d.activeCell initial i).count : ℝ) * (C / (1 + a) ^ P) := by
    intro i hi l _
    have hb := hbound a U ha T K hK d initial i (hρ i hi) (l.1 + l.2) E
    unfold tailCellDescendantDifference at hb
    convert hb using 1 <;> ring
  have hb := activeSlot_primaryDescendant_error_le d initial I φ E F
    (C / (1 + a) ^ P) hlocal
  convert hb using 1 <;> ring

/-- A finite selection may depend on the descendant level. This preserves
the energy window needed for reference-mass bounds: cells near energy `E-q`
are counted only with that descendant level, instead of replacing the mass
by a rectangular cell-by-level overestimate. -/
theorem exists_uniform_selectedPair_error_le (φ : SmoothKernel) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a U : ℝ), 0 ≤ a → ∀ (T K : ℕ), 0 < K →
      ∀ (d : RealTailLocalData a U T (realTailMomentDegree K a))
        (initial : FiniteRepairState)
        (I : Finset (d.ActiveSlot initial × (ℕ × ℕ))),
      (∀ p ∈ I, ∀ᵐ u ∂(referenceMeasure p.1.val.row).restrict
        (Ioo ((d.slotPreState initial p.1.val).front p.1.val.row)
          (d.activeCell initial p.1).right),
        0 ≤ (d.slotPreState initial p.1.val).numerator p.1.val.row u) →
      ∀ E : ℝ,
      |(∑ p ∈ I, (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
          ∑ n, descendantTest φ (p.2.1 + p.2.2) E ((d.activeCell initial p.1).node n)) -
        ∑ p ∈ I, (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
          ∫ u in Ioo ((d.slotPreState initial p.1.val).front p.1.val.row)
              (d.activeCell initial p.1).right,
            (d.slotPreState initial p.1.val).numerator p.1.val.row u *
              descendantTest φ (p.2.1 + p.2.2) E u ∂referenceMeasure p.1.val.row| ≤
        C * (∑ p ∈ I, (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
          (d.activeCell initial p.1).count) / (1 + a) ^ P := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_activeCell_error_le φ P
  refine ⟨C, hC, ?_⟩
  intro a U ha T K hK d initial I hρ E
  have hb := abs_weighted_sum_sub_le I
    (fun p => (partitionCount p.2.1 * partitionCount p.2.2 : ℝ))
    (fun p => ((d.activeCell initial p.1).count : ℝ))
    (fun p => ∑ n, descendantTest φ (p.2.1 + p.2.2) E
      ((d.activeCell initial p.1).node n))
    (fun p => ∫ u in Ioo ((d.slotPreState initial p.1.val).front p.1.val.row)
      (d.activeCell initial p.1).right,
      (d.slotPreState initial p.1.val).numerator p.1.val.row u *
        descendantTest φ (p.2.1 + p.2.2) E u ∂referenceMeasure p.1.val.row)
    (C / (1 + a) ^ P) (fun p _ => by positivity) (fun p hp => ?_)
  · convert hb using 1 <;> ring
  · have hb := hbound a U ha T K hK d initial p.1 (hρ p hp) (p.2.1 + p.2.2) E
    unfold tailCellDescendantDifference at hb
    convert hb using 1 <;> ring

/-- The main selected-pair estimate for all actual cells, including signed
cells near spin openings. Its only mass term is the true absolute continuum
mass on each relevant cell. It can be bounded separately by the leading
density plus the proved error envelope, without asserting positivity. -/
theorem exists_uniform_selectedPair_absMass_error_le (φ : SmoothKernel) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a U : ℝ), 0 ≤ a → ∀ (T K : ℕ), 0 < K →
      ∀ (d : RealTailLocalData a U T (realTailMomentDegree K a))
        (initial : FiniteRepairState)
        (I : Finset (d.ActiveSlot initial × (ℕ × ℕ))) (E : ℝ),
      |(∑ p ∈ I, (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
          ∑ n, descendantTest φ (p.2.1 + p.2.2) E ((d.activeCell initial p.1).node n)) -
        ∑ p ∈ I, (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
          ∫ u in Ioo ((d.slotPreState initial p.1.val).front p.1.val.row)
              (d.activeCell initial p.1).right,
            (d.slotPreState initial p.1.val).numerator p.1.val.row u *
              descendantTest φ (p.2.1 + p.2.2) E u ∂referenceMeasure p.1.val.row| ≤
        C * (∑ p ∈ I, (partitionCount p.2.1 * partitionCount p.2.2 : ℝ) *
          tailCellAbsoluteMass (d.activeCell initial p.1)) / (1 + a) ^ P := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_tailCell_absMass_error_le φ P
  refine ⟨C, hC, ?_⟩
  intro a U ha T K hK d initial I E
  have hb := abs_weighted_sum_sub_le I
    (fun p => (partitionCount p.2.1 * partitionCount p.2.2 : ℝ))
    (fun p => tailCellAbsoluteMass (d.activeCell initial p.1))
    (fun p => ∑ n, descendantTest φ (p.2.1 + p.2.2) E
      ((d.activeCell initial p.1).node n))
    (fun p => ∫ u in Ioo ((d.slotPreState initial p.1.val).front p.1.val.row)
      (d.activeCell initial p.1).right,
      (d.slotPreState initial p.1.val).numerator p.1.val.row u *
        descendantTest φ (p.2.1 + p.2.2) E u ∂referenceMeasure p.1.val.row)
    (C / (1 + a) ^ P) (fun p _ => by positivity) (fun p _ => ?_)
  · convert hb using 1 <;> ring
  · have hb := hbound a ha p.1.val.row _ _ _ (d.activeCell initial p.1)
      p.1.property.physical (realTailMomentDegree_ge_charge hK a p.1.val.layer)
      (p.2.1 + p.2.2) E
    unfold tailCellDescendantDifference at hb
    convert hb using 1 <;> ring

end BTZEntropy.Comparison
