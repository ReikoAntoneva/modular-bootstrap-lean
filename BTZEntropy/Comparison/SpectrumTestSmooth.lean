import BTZEntropy.Comparison.SpectrumTestObservable
import BTZEntropy.Comparison.SpectrumTestCell

/-! Descendant packets on the actual public spectrum stabilize to the literal
finite construction. The same cutoff works uniformly on an energy window. -/

noncomputable section
open GapFamily GapFamily.Construction
open scoped Classical

namespace BTZEntropy.Comparison

/-- Finite-fibre regrouping and layer escape give exact stabilization of a
finite descendant packet on the original public spectrum. -/
theorem primaryFiniteLevelCount_eq_prefix (φ : SmoothKernel)
    {b : ℝ} (D : PermanentSpectrumData b) (c E R : ℝ) (F : Finset (ℕ × ℕ))
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (N : ℕ)
    (hN : E + R + 1 / 12 < (N : ℝ)) :
    primaryFiniteLevelCount φ c (D.spectrum c) E F =
      ((D.permanentAtomList N).map (fun p => primaryDescendantTest φ E F p.1)).sum := by
  rw [primaryFiniteLevelCount_permanentSpectrum_eq]
  exact permanentNodeTest_eq_prefix D (fun p => primaryDescendantTest φ E F p.1) N
    (fun p hp => primaryDescendantTest_eq_zero_of_lt φ E R p.1 F hR (hN.trans_le hp)) N le_rfl

/-- A single prefix suffices for every energy below the upper edge of a
window and every finite descendant packet, including arbitrary multiplicity. -/
theorem primaryFiniteLevelCount_uniform_prefix (φ : SmoothKernel)
    {b : ℝ} (D : PermanentSpectrumData b) (c Emax : ℝ) :
    ∃ N : ℕ, ∀ E : ℝ, E ≤ Emax → ∀ F : Finset (ℕ × ℕ),
      primaryFiniteLevelCount φ c (D.spectrum c) E F =
        ((D.permanentAtomList N).map (fun p => primaryDescendantTest φ E F p.1)).sum := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (Emax + R + 1 / 12)
  refine ⟨N, ?_⟩
  intro E hE F
  exact primaryFiniteLevelCount_eq_prefix φ D c E R F
    (fun u hu => hR (subset_tsupport φ hu)) N (by linarith)

/-- The full observable uses one finite cutoff uniformly over every permanent
spectrum and every energy below the window edge. In particular, the cutoff
does not depend on a marker position or on any quadrature-node selector. -/
theorem smoothCount_uniform_permanentPrefix (φ : SmoothKernel) (c Emax : ℝ) :
    ∃ N : ℕ, ∀ (b : ℝ) (D : PermanentSpectrumData b) (E : ℝ), E ≤ Emax →
      smoothCount φ c (D.spectrum c) E =
        vacuumFiniteLevelCount φ c E (descendantLevelCutoff N) +
        ((D.permanentAtomList N).map
          (fun p => primaryDescendantTest φ E (descendantLevelCutoff N) p.1)).sum := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (max (Emax + R + c / 12) (Emax + R + 1 / 12))
  refine ⟨N, ?_⟩
  intro b D E hE
  have hNv : E + R + c / 12 < (N : ℝ) := by
    linarith [le_max_left (Emax + R + c / 12) (Emax + R + 1 / 12)]
  have hNp : E + R + 1 / 12 < (N : ℝ) := by
    linarith [le_max_right (Emax + R + c / 12) (Emax + R + 1 / 12)]
  rw [smoothCount_permanentSpectrum_eq_of_cutoff φ D c E R N
    (fun u hu => hR (subset_tsupport φ hu)) hNv hNp]
  congr 1
  exact permanentNodeTest_eq_prefix D
    (fun p => primaryDescendantTest φ E (descendantLevelCutoff N) p.1) N
    (fun p hp => primaryDescendantTest_eq_zero_of_lt φ E R p.1 _
      (fun u hu => hR (subset_tsupport φ hu)) (hNp.trans_le hp)) N le_rfl

/-- Exchanging two genuinely finite sums leaves the exact descendant
partition multiplicity in front of each actual unit-node test. -/
theorem sum_primaryDescendantTest {ι : Type*} [Fintype ι]
    (φ : SmoothKernel) (E : ℝ) (F : Finset (ℕ × ℕ)) (x : ι → ℝ) :
    (∑ i, primaryDescendantTest φ E F (x i)) =
      ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
        ∑ i, φ (x i - 1 / 12 + (l.1 : ℝ) + (l.2 : ℝ) - E) := by
  simp only [primaryDescendantTest]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]

variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
  (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)

/-- The observable on the actual spectrum separates into marker, initial
packet and literal cell tests, with no new spectrum or node selection. -/
theorem primaryFiniteLevelCount_eq_initial_add_cell
    (b : ℝ) (hb : 0 ≤ b) (hbT : b ≤ (T : ℝ))
    (hinitial : ∀ p ∈ initial.nodes, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (φ : SmoothKernel) (c E R : ℝ) (F : Finset (ℕ × ℕ))
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (k : ℕ)
    (hk : E + R + 1 / 12 < ((T + k : ℕ) : ℝ)) :
    primaryFiniteLevelCount φ c
      ((d.permanentSpectrumData b hb hbT initial hinitial).spectrum c) E F =
      primaryDescendantTest φ E F b +
        (initial.nodes.map (fun p => primaryDescendantTest φ E F p.1)).sum +
        ∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
          scheduledCellTest d initial (fun p => primaryDescendantTest φ E F p.1) ⟨m, q⟩ := by
  rw [primaryFiniteLevelCount_permanentSpectrum_eq]
  exact realPermanentNodeTest_eq_initial_add_cell d initial b hb hbT hinitial
    (fun p => primaryDescendantTest φ E F p.1) ((T + k : ℕ) : ℝ)
    (fun p hp => primaryDescendantTest_eq_zero_of_lt φ E R p.1 F hR (hk.trans_le hp)) k
    le_rfl

/-- Each actual cell's descendant packet is a finite partition-weighted sum
of precisely the scalar tests controlled by the moment approximation lemma. -/
theorem scheduledCellTest_primaryDescendantTest (φ : SmoothKernel) (E : ℝ)
    (F : Finset (ℕ × ℕ)) (p : LayerSlotIndex T) :
    scheduledCellTest d initial (fun q => primaryDescendantTest φ E F q.1) p =
      ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
        scheduledCellTest d initial
          (fun q => φ (q.1 - 1 / 12 + (l.1 : ℝ) + (l.2 : ℝ) - E)) p := by
  unfold scheduledCellTest
  split_ifs with h
  · exact sum_primaryDescendantTest φ E F (d.cell _ _ _ h).node
  · simp

/-- The complete full-state observable, including all vacuum descendants,
is exactly the marker, initial packet and actual cell expansion once both
finite cutoffs contain the test window. -/
theorem smoothCount_eq_initial_add_cell
    (b : ℝ) (hb : 0 ≤ b) (hbT : b ≤ (T : ℝ))
    (hinitial : ∀ p ∈ initial.nodes, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (φ : SmoothKernel) (c E R : ℝ) (N k : ℕ)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hNv : E + R + c / 12 < (N : ℝ))
    (hNp : E + R + 1 / 12 < (N : ℝ))
    (hk : E + R + 1 / 12 < ((T + k : ℕ) : ℝ)) :
    smoothCount φ c ((d.permanentSpectrumData b hb hbT initial hinitial).spectrum c) E =
      vacuumFiniteLevelCount φ c E (descendantLevelCutoff N) +
      primaryDescendantTest φ E (descendantLevelCutoff N) b +
      (initial.nodes.map (fun p => primaryDescendantTest φ E (descendantLevelCutoff N) p.1)).sum +
      ∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (T + m)).length,
        scheduledCellTest d initial
          (fun p => primaryDescendantTest φ E (descendantLevelCutoff N) p.1) ⟨m, q⟩ := by
  rw [smoothCount_permanentSpectrum_eq_of_cutoff φ _ c E R N hR hNv hNp]
  rw [realPermanentNodeTest_eq_initial_add_cell d initial b hb hbT hinitial
    (fun p => primaryDescendantTest φ E (descendantLevelCutoff N) p.1)
    ((T + k : ℕ) : ℝ)
    (fun p hp => primaryDescendantTest_eq_zero_of_lt φ E R p.1 _ hR (hk.trans_le hp))
    k le_rfl]
  simp only [add_assoc]

/-- On any bounded energy window a common finite descendant packet and
finite construction prefix give the original full-state count exactly. -/
theorem smoothCount_uniform_initial_add_cell
    (b : ℝ) (hb : 0 ≤ b) (hbT : b ≤ (T : ℝ))
    (hinitial : ∀ p ∈ initial.nodes, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (φ : SmoothKernel) (c Emax : ℝ) :
    ∃ N : ℕ, ∀ E : ℝ, E ≤ Emax →
      smoothCount φ c ((d.permanentSpectrumData b hb hbT initial hinitial).spectrum c) E =
        vacuumFiniteLevelCount φ c E (descendantLevelCutoff N) +
        primaryDescendantTest φ E (descendantLevelCutoff N) b +
        (initial.nodes.map (fun p => primaryDescendantTest φ E (descendantLevelCutoff N) p.1)).sum +
        ∑ m ∈ Finset.range N, ∑ q : Fin (layerSlots (T + m)).length,
          scheduledCellTest d initial
            (fun p => primaryDescendantTest φ E (descendantLevelCutoff N) p.1) ⟨m, q⟩ := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (max (Emax + R + c / 12) (Emax + R + 1 / 12))
  refine ⟨N, ?_⟩
  intro E hE
  have hNv : E + R + c / 12 < (N : ℝ) := by
    linarith [le_max_left (Emax + R + c / 12) (Emax + R + 1 / 12)]
  have hNp : E + R + 1 / 12 < (N : ℝ) := by
    linarith [le_max_right (Emax + R + c / 12) (Emax + R + 1 / 12)]
  apply smoothCount_eq_initial_add_cell d initial b hb hbT hinitial φ c E R N N
    (fun u hu => hR (subset_tsupport φ hu)) hNv hNp
  exact hNp.trans_le (by exact_mod_cast (Nat.le_add_left N T))

end BTZEntropy.Comparison
