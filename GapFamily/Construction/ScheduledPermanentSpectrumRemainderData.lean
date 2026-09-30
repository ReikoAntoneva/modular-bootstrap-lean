import GapFamily.Construction.ScheduledPermanentSpectrum
import GapFamily.Construction.PermanentSpectrumRemainderAtomList

/-! Exact finite histories and thermal series for the spectrum made from
the actual scheduled lists, with empty absolute layers before its start. -/

noncomputable section
namespace GapFamily.Construction

/-- Flattening an absolute-index layer family discards exactly its empty
padding and retains the original ordered layer blocks. -/
theorem flatMap_range_zero_padded {α : Type*} (block : ℕ → List α) (T n : ℕ) :
    (List.range (T + n)).flatMap
      (fun m => if T ≤ m then block (m - T) else []) =
      (List.range n).flatMap block := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]
  have hleft : (List.range T).flatMap
      (fun m => if T ≤ m then block (m - T) else []) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro m hm
    simp [Nat.not_le.mpr (List.mem_range.mp hm)]
  simp [hleft]

variable {S : Type*}
variable (b : ℝ) (hb : 0 ≤ b) (T : ℕ) (hbT : b ≤ (T : ℝ))
  (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S)
  (node : ℕ → ℤ → S → List (ℝ × ℤ)) (initial : S)
  (initialAtoms : List (ℝ × ℤ)) (P : S → Prop)
  (C : ∀ m, T ≤ m → LayerCellContract m front (update m) P)
  (hP : P initial) (hf : FrontInvariant T front initial)
  (hinitial : ∀ p ∈ initialAtoms, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
  (hnode : ∀ m, T ≤ m → ∀ s j, P s → CanExecute m front s j →
    ∀ p ∈ node m j s, front s j ≤ p.1 ∧ p.1 ≤ front s j + 1 ∧ p.2 = j)

/-- At absolute stage `T + n`, the permanent spectrum retains the marker
followed by the exact scheduled atom history after `n` executed layers. -/
theorem scheduledPermanentSpectrumData_permanentAtomList (n : ℕ) :
    (scheduledPermanentSpectrumData b hb T hbT front update node initial initialAtoms
      P C hP hf hinitial hnode).permanentAtomList (T + n) =
      (b, 0) :: scheduledNodePrefix T front update node initial initialAtoms n := by
  rw [scheduledPermanentSpectrumData, PermanentSpectrumData.ofLists_permanentAtomList]
  change (b, 0) :: (initialAtoms ++ (List.range (T + n)).flatMap
    (fun m => if T ≤ m then scheduledLayerBlock T front update node initial (m - T)
      else [])) = _
  rw [flatMap_range_zero_padded]
  simp only [scheduledNodePrefix, atomBlockPrefix, appendAtomBlocks, List.flatMap_def]

/-- The thermal mass of absolute layer `T + n` is exactly the thermal sum
of the actual emitted layer list at schedule stage `n`. -/
theorem scheduledPermanentSpectrumData_layerThermal_add (t : ℝ) (n : ℕ) :
    (scheduledPermanentSpectrumData b hb T hbT front update node initial initialAtoms
      P C hP hf hinitial hnode).layerThermal t (T + n) =
      ((scheduledLayerBlock T front update node initial n).map
        (fun p => Real.exp (-t * p.1))).sum := by
  rw [scheduledPermanentSpectrumData, PermanentSpectrumData.ofLists_layerThermal,
    scheduledAbsoluteLayerBlock_add]

/-- Summability of the literal emitted layer masses supplies summability of
the same permanent spectrum's absolute-index layer masses. -/
theorem summable_scheduledPermanentSpectrumData_layerThermal (t : ℝ)
    (hsum : Summable (fun n =>
      ((scheduledLayerBlock T front update node initial n).map
        (fun p => Real.exp (-t * p.1))).sum)) :
    Summable ((scheduledPermanentSpectrumData b hb T hbT front update node initial
      initialAtoms P C hP hf hinitial hnode).layerThermal t) := by
  have hshift : Summable (fun n =>
      (scheduledPermanentSpectrumData b hb T hbT front update node initial initialAtoms
        P C hP hf hinitial hnode).layerThermal t (T + n)) := by
    simpa only [scheduledPermanentSpectrumData_layerThermal_add] using hsum
  apply (summable_nat_add_iff T).mp
  simpa only [Nat.add_comm] using hshift

end GapFamily.Construction
