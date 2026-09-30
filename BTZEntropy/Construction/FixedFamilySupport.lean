import GapFamily.Construction.RealPermanentSpectrumData

/-!
# Support above a fixed clearing cutoff

The support bounds below apply to the actual permanent unit-node spectrum.
Passing to its support uses the coordinate range, so coincident occurrences
retain the same finite-fibre multiplicity used in the gap construction.
-/

noncomputable section

namespace BTZEntropy.Construction

open GapFamily GapFamily.Construction

/-- If every initial and tail occurrence is above `B`, every supported
coordinate other than the scalar marker has shifted energy above `B`. -/
theorem permanentSpectrumData_support_energy_gt_cutoff {δ : ℝ}
    (D : PermanentSpectrumData δ) (B c : ℝ)
    (hinitial : ∀ i, B < D.initialEnergy i)
    (hlayer : ∀ m i, B < D.layerEnergy m i)
    (p : ℝ × ℝ) (hp : p ∈ (D.spectrum c).support)
    (hne : p ≠ ((shift c + δ) / 2, (shift c + δ) / 2)) :
    B < GapFamily.energy c p := by
  obtain ⟨i, rfl⟩ := hp
  rw [energy_nodeCoordinate]
  rcases i with u | i | ⟨m, i⟩
  · exact False.elim (hne (by
      cases u
      change nodeCoordinate c D.energy D.spin D.marker = _
      simp [nodeCoordinate]))
  · exact hinitial i
  · exact hlayer m i

/-- For the real repair recursion, a fixed lower bound on the actual initial
list and a tail start above `B` imply the same support exclusion. The marker
parameter `δ` need not equal the clearing cutoff. -/
theorem realPermanentSpectrumData_support_energy_gt_cutoff
    {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
    (d : RealTailLocalData a U T degree) (δ B c : ℝ)
    (hδ : 0 ≤ δ) (hδT : δ ≤ (T : ℝ)) (initial : FiniteRepairState)
    (hinitial : ∀ p ∈ initial.nodes, δ ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (hinitialCutoff : ∀ p ∈ initial.nodes, B < p.1) (hBT : B < (T : ℝ))
    (p : ℝ × ℝ)
    (hp : p ∈ ((d.permanentSpectrumData δ hδ hδT initial hinitial).spectrum c).support)
    (hne : p ≠ ((shift c + δ) / 2, (shift c + δ) / 2)) :
    B < GapFamily.energy c p := by
  apply permanentSpectrumData_support_energy_gt_cutoff
    (d.permanentSpectrumData δ hδ hδT initial hinitial) B c ?_ ?_ p hp hne
  · intro i
    exact hinitialCutoff _ (List.get_mem initial.nodes i)
  · intro m i
    exact d.scheduledAbsoluteLayerBlock_strict initial B hBT m _ (List.get_mem _ i)

end BTZEntropy.Construction
