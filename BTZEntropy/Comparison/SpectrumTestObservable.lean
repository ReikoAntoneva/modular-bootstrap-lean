import BTZEntropy.Observable
import GapFamily.Construction.PermanentSpectrumData

/-!
# Descendant tests on the permanent spectrum

A finite packet of descendant levels turns the full-state kernel into a test
of the reduced primary energy. The public spectrum uses the actual cardinality
of each coordinate fibre, so its weighted test sum equals the sum over all
literal unit-node occurrences, including coincident nodes.
-/

noncomputable section

namespace BTZEntropy

open GapFamily GapFamily.Construction

/-- A finite descendant packet as a test of reduced primary energy. The
`1 / 12` shift is the exact difference from physical cylinder energy. -/
def primaryDescendantTest (φ : SmoothKernel) (E : ℝ)
    (F : Finset (ℕ × ℕ)) (x : ℝ) : ℝ :=
  ∑ l ∈ F, (partitionCount l.1 * partitionCount l.2 : ℝ) *
    φ (x - 1 / 12 + (l.1 : ℝ) + (l.2 : ℝ) - E)

/-- The weighted public primary count for a fixed finite descendant packet. -/
def primaryFiniteLevelCount (φ : SmoothKernel) (c : ℝ) (s : Spectrum)
    (E : ℝ) (F : Finset (ℕ × ℕ)) : ℝ :=
  ∑' p : s.support, (s.multiplicity p : ℝ) *
    primaryDescendantTest φ E F (energy c p)

theorem primaryDescendantTest_nonneg (φ : SmoothKernel) (E : ℝ)
    (F : Finset (ℕ × ℕ)) (x : ℝ) :
    0 ≤ primaryDescendantTest φ E F x := by
  apply Finset.sum_nonneg
  intro l hl
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (φ.nonneg _)

/-- An upper support bound for the kernel gives one bound for every packet. -/
theorem primaryDescendantTest_eq_zero_of_lt (φ : SmoothKernel) (E R x : ℝ)
    (F : Finset (ℕ × ℕ)) (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hx : E + R + 1 / 12 < x) :
    primaryDescendantTest φ E F x = 0 := by
  apply Finset.sum_eq_zero
  intro l hl
  have hz : φ (x - 1 / 12 + (l.1 : ℝ) + (l.2 : ℝ) - E) = 0 := by
    by_contra hn
    have hb := hR _ hn
    linarith [Nat.cast_nonneg (α := ℝ) l.1, Nat.cast_nonneg (α := ℝ) l.2]
  rw [hz, mul_zero]

theorem primaryDescendantTest_node_hasFiniteSupport (φ : SmoothKernel)
    {b : ℝ} (D : PermanentSpectrumData b) (E : ℝ) (F : Finset (ℕ × ℕ)) :
    Function.HasFiniteSupport (fun i : D.Node =>
      primaryDescendantTest φ E F (D.energy i)) := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  apply (D.energy_sublevel_finite (E + R + 1 / 12)).subset
  intro i hi
  change D.energy i ≤ E + R + 1 / 12
  by_contra hn
  exact hi (primaryDescendantTest_eq_zero_of_lt φ E R (D.energy i) F
    (fun u hu => hR (subset_tsupport φ hu)) (lt_of_not_ge hn))

theorem primaryDescendantTest_node_summable (φ : SmoothKernel)
    {b : ℝ} (D : PermanentSpectrumData b) (E : ℝ) (F : Finset (ℕ × ℕ)) :
    Summable (fun i : D.Node => primaryDescendantTest φ E F (D.energy i)) :=
  summable_of_hasFiniteSupport (primaryDescendantTest_node_hasFiniteSupport φ D E F)

/-- Finite-fibre regrouping preserves the full primary multiplicity in each
descendant packet. Neither modularity nor thermal summability is needed. -/
theorem primaryFiniteLevelCount_permanentSpectrum_eq (φ : SmoothKernel)
    {b : ℝ} (D : PermanentSpectrumData b) (c E : ℝ) (F : Finset (ℕ × ℕ)) :
    primaryFiniteLevelCount φ c (D.spectrum c) E F =
      ∑' i : D.Node, primaryDescendantTest φ E F (D.energy i) := by
  have hsum : Summable (fun i : D.Node =>
      primaryDescendantTest φ E F (energy c (nodeCoordinate c D.energy D.spin i))) := by
    simpa only [energy_nodeCoordinate] using primaryDescendantTest_node_summable φ D E F
  simpa only [primaryFiniteLevelCount, PermanentSpectrumData.spectrum, nodeSpectrum,
    nsmul_eq_mul, energy_nodeCoordinate] using
    coordinateSpectrum_tsum
      (nodeCoordinate_locallyFinite c D.energy D.spin D.energy_sublevel_finite)
      (fun p => primaryDescendantTest φ E F (energy c p)) hsum

/-- The square packet containing every left and right level up to `N`. -/
def descendantLevelCutoff (N : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (N + 1) ×ˢ Finset.range (N + 1)

@[simp] theorem mem_descendantLevelCutoff (N : ℕ) (l : ℕ × ℕ) :
    l ∈ descendantLevelCutoff N ↔ l.1 ≤ N ∧ l.2 ≤ N := by
  simp [descendantLevelCutoff]

theorem permanentSpectrum_energy_nonneg {b : ℝ} (D : PermanentSpectrumData b)
    (c : ℝ) (p : (D.spectrum c).support) : 0 ≤ energy c p := by
  obtain ⟨i, hi⟩ := p.property
  rw [← hi, energy_nodeCoordinate]
  exact D.marker_nonneg.trans (D.energy_lower i)

/-- Local finiteness and nonnegative reduced primary energy suffice for the
full-state observable. No character or modularity property is used. -/
theorem smoothTerm_permanentSpectrum_hasFiniteSupport (φ : SmoothKernel)
    {b : ℝ} (D : PermanentSpectrumData b) (c E : ℝ) :
    Function.HasFiniteSupport (smoothTerm φ c (D.spectrum c) E) := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (max (E + R + c / 12) (E + R + 1 / 12))
  have hNv : E + R + c / 12 < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hNp : E + R + 1 / 12 < (N : ℝ) := (le_max_right _ _).trans_lt hN
  let P : Set (D.spectrum c).support := {p | energy c p ≤ (N : ℝ)}
  let L : Set (ℕ × ℕ) := Set.Iic N ×ˢ Set.Iic N
  have hP : P.Finite := by
    have h := (D.support_locally_finite c (shift c + N)).preimage
      (f := fun p : (D.spectrum c).support => p.val) (fun _ _ _ _ h => Subtype.ext h)
    apply h.subset
    intro p hp
    exact ⟨p.property, by dsimp [P, energy] at hp; dsimp; linarith⟩
  have hL : L.Finite := (Set.finite_Iic N).prod (Set.finite_Iic N)
  have hfin : (Sum.inl '' L ∪ Sum.inr '' (P ×ˢ L) :
      Set (StateLevel (D.spectrum c))).Finite :=
    (hL.image Sum.inl).union ((hP.prod hL).image Sum.inr)
  apply hfin.subset
  intro v hv
  change smoothTerm φ c (D.spectrum c) E v ≠ 0 at hv
  have hφ : φ (stateEnergy c (D.spectrum c) v - E) ≠ 0 :=
    (mul_ne_zero_iff.mp hv).2
  have hbound := hR (subset_tsupport φ hφ)
  rcases v with ⟨nL, nR⟩ | ⟨p, nL, nR⟩
  · dsimp [stateEnergy] at hbound
    have hnL : nL ≤ N := by
      apply (Nat.cast_le (α := ℝ)).mp
      linarith [Nat.cast_nonneg (α := ℝ) nR]
    have hnR : nR ≤ N := by
      apply (Nat.cast_le (α := ℝ)).mp
      linarith [Nat.cast_nonneg (α := ℝ) nL]
    exact Or.inl ⟨(nL, nR), ⟨hnL, hnR⟩, rfl⟩
  · rw [stateEnergy_primary] at hbound
    have hp := permanentSpectrum_energy_nonneg D c p
    have hpN : energy c p ≤ (N : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) nL, Nat.cast_nonneg (α := ℝ) nR]
    have hnL : nL ≤ N := by
      apply (Nat.cast_le (α := ℝ)).mp
      linarith [Nat.cast_nonneg (α := ℝ) nR]
    have hnR : nR ≤ N := by
      apply (Nat.cast_le (α := ℝ)).mp
      linarith [Nat.cast_nonneg (α := ℝ) nL]
    exact Or.inr ⟨(p, nL, nR), ⟨hpN, hnL, hnR⟩, rfl⟩

theorem smoothTerm_permanentSpectrum_summable (φ : SmoothKernel)
    {b : ℝ} (D : PermanentSpectrumData b) (c E : ℝ) :
    Summable (smoothTerm φ c (D.spectrum c) E) :=
  summable_of_hasFiniteSupport (smoothTerm_permanentSpectrum_hasFiniteSupport φ D c E)

/-- The vacuum contribution on a finite descendant packet, with its null
level-one descendants removed by `vacuumPartitionCount`. -/
def vacuumFiniteLevelCount (φ : SmoothKernel) (c E : ℝ)
    (F : Finset (ℕ × ℕ)) : ℝ :=
  ∑ l ∈ F, (vacuumPartitionCount l.1 * vacuumPartitionCount l.2 : ℝ) *
    φ ((l.1 : ℝ) + (l.2 : ℝ) - c / 12 - E)

/-- A common descendant cutoff gives the actual full smooth count as its
vacuum packet plus the packet test on every literal permanent node. -/
theorem smoothCount_permanentSpectrum_eq_of_cutoff (φ : SmoothKernel)
    {b : ℝ} (D : PermanentSpectrumData b) (c E R : ℝ) (N : ℕ)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hNv : E + R + c / 12 < (N : ℝ))
    (hNp : E + R + 1 / 12 < (N : ℝ)) :
    smoothCount φ c (D.spectrum c) E =
      vacuumFiniteLevelCount φ c E (descendantLevelCutoff N) +
        ∑' i : D.Node, primaryDescendantTest φ E (descendantLevelCutoff N) (D.energy i) := by
  have hsum := smoothTerm_permanentSpectrum_summable φ D c E
  have hleft := hsum.comp_injective Sum.inl_injective
  have hright : Summable (fun p : (D.spectrum c).support × (ℕ × ℕ) =>
      smoothTerm φ c (D.spectrum c) E (.inr p)) :=
    hsum.comp_injective Sum.inr_injective
  have hv : (∑' l : ℕ × ℕ, smoothTerm φ c (D.spectrum c) E (.inl l)) =
      vacuumFiniteLevelCount φ c E (descendantLevelCutoff N) := by
    calc
      _ = ∑ l ∈ descendantLevelCutoff N,
          smoothTerm φ c (D.spectrum c) E (.inl l) := by
        apply tsum_eq_sum
        intro l hl
        have hz : φ ((l.1 : ℝ) + (l.2 : ℝ) - c / 12 - E) = 0 := by
          by_contra hn
          have hb := hR _ hn
          apply hl
          rw [mem_descendantLevelCutoff]
          constructor <;> apply (Nat.cast_le (α := ℝ)).mp
          · linarith [Nat.cast_nonneg (α := ℝ) l.2]
          · linarith [Nat.cast_nonneg (α := ℝ) l.1]
        simp [smoothTerm, stateEnergy, hz]
      _ = _ := by simp only [vacuumFiniteLevelCount, smoothTerm, stateMultiplicity,
        stateEnergy, Nat.cast_mul]
  have hp (p : (D.spectrum c).support) :
      (∑' l : ℕ × ℕ, smoothTerm φ c (D.spectrum c) E (.inr (p, l))) =
        ((D.spectrum c).multiplicity p : ℝ) *
          primaryDescendantTest φ E (descendantLevelCutoff N) (energy c p) := by
    calc
      _ = ∑ l ∈ descendantLevelCutoff N,
          smoothTerm φ c (D.spectrum c) E (.inr (p, l)) := by
        apply tsum_eq_sum
        intro l hl
        have hz : φ (energy c p - 1 / 12 + (l.1 : ℝ) + (l.2 : ℝ) - E) = 0 := by
          by_contra hn
          have hb := hR _ hn
          have he := permanentSpectrum_energy_nonneg D c p
          apply hl
          rw [mem_descendantLevelCutoff]
          constructor <;> apply (Nat.cast_le (α := ℝ)).mp
          · linarith [Nat.cast_nonneg (α := ℝ) l.2]
          · linarith [Nat.cast_nonneg (α := ℝ) l.1]
        rcases l with ⟨nL, nR⟩
        simp only [smoothTerm, stateEnergy_primary, hz, mul_zero]
      _ = _ := by
        simp only [primaryDescendantTest, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        rcases l with ⟨nL, nR⟩
        simp only [smoothTerm, stateMultiplicity, stateEnergy_primary, Nat.cast_mul]
        ring
  rw [smoothCount, Summable.tsum_sum (f := smoothTerm φ c (D.spectrum c) E)
    hleft hright, hright.tsum_prod, hv]
  simp_rw [hp]
  exact congrArg (vacuumFiniteLevelCount φ c E (descendantLevelCutoff N) + ·)
    (primaryFiniteLevelCount_permanentSpectrum_eq φ D c E (descendantLevelCutoff N))

/-- Compact support always supplies a common finite descendant packet for
the whole permanent spectrum and its vacuum. -/
theorem smoothCount_permanentSpectrum_eq_finite_packet (φ : SmoothKernel)
    {b : ℝ} (D : PermanentSpectrumData b) (c E : ℝ) :
    ∃ N : ℕ, smoothCount φ c (D.spectrum c) E =
      vacuumFiniteLevelCount φ c E (descendantLevelCutoff N) +
        ∑' i : D.Node, primaryDescendantTest φ E (descendantLevelCutoff N) (D.energy i) := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (max (E + R + c / 12) (E + R + 1 / 12))
  exact ⟨N, smoothCount_permanentSpectrum_eq_of_cutoff φ D c E R N
    (fun u hu => hR (subset_tsupport φ hu))
    ((le_max_left _ _).trans_lt hN) ((le_max_right _ _).trans_lt hN)⟩

end BTZEntropy
