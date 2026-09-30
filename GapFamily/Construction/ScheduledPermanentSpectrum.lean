import GapFamily.Construction.LayerScheduleNode
import GapFamily.Construction.PermanentSpectrumData

/-!
# Permanent spectrum data from the actual layer schedule

The spectrum data uses the lengths and coordinates of the literal emitted
lists. The only hypotheses are initial finite-node bounds and local cell update
and emission contracts; the schedule supplies all complete-layer bounds.
-/

noncomputable section
namespace GapFamily.Construction

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

/-- The actual scheduled initial and layer lists, with their literal `Fin length`
indices, provide permanent spectrum data while retaining repeated coordinates. -/
def scheduledPermanentSpectrumData : PermanentSpectrumData b :=
  PermanentSpectrumData.ofLists hb initialAtoms
    (scheduledAbsoluteLayerBlock T front update node initial) hinitial
    (scheduledAbsoluteLayerBlock_spectrum_bounds T front update node initial P b hbT
      C hP hf hnode)

@[simp] theorem scheduledPermanentSpectrumData_initialCount :
    (scheduledPermanentSpectrumData b hb T hbT front update node initial initialAtoms
      P C hP hf hinitial hnode).initialCount = initialAtoms.length := rfl

@[simp] theorem scheduledPermanentSpectrumData_layerCount (m : ℕ) :
    (scheduledPermanentSpectrumData b hb T hbT front update node initial initialAtoms
      P C hP hf hinitial hnode).layerCount m =
        (scheduledAbsoluteLayerBlock T front update node initial m).length := rfl

/-- A generated layer has exactly as many indexed atoms as were actually emitted. -/
theorem scheduledPermanentSpectrumData_layerCount_add (n : ℕ) :
    (scheduledPermanentSpectrumData b hb T hbT front update node initial initialAtoms
      P C hP hf hinitial hnode).layerCount (T + n) =
        (scheduledLayerBlock T front update node initial n).length := by
  rw [scheduledPermanentSpectrumData_layerCount, scheduledAbsoluteLayerBlock_add]

/-- No artificial nodes are inserted into the empty layers before the start. -/
theorem scheduledPermanentSpectrumData_layerCount_of_lt {m : ℕ} (hm : m < T) :
    (scheduledPermanentSpectrumData b hb T hbT front update node initial initialAtoms
      P C hP hf hinitial hnode).layerCount m = 0 := by
  simp [scheduledPermanentSpectrumData_layerCount, scheduledAbsoluteLayerBlock, Nat.not_le.mpr hm]

/-- The stored energy is the coordinate of the actual list occurrence. -/
@[simp] theorem scheduledPermanentSpectrumData_layerEnergy (m : ℕ)
    (i : Fin ((scheduledAbsoluteLayerBlock T front update node initial m).length)) :
    (scheduledPermanentSpectrumData b hb T hbT front update node initial initialAtoms
      P C hP hf hinitial hnode).layerEnergy m i =
        ((scheduledAbsoluteLayerBlock T front update node initial m).get i).1 := rfl

/-- The stored spin is the coordinate of the same actual list occurrence. -/
@[simp] theorem scheduledPermanentSpectrumData_layerSpin (m : ℕ)
    (i : Fin ((scheduledAbsoluteLayerBlock T front update node initial m).length)) :
    (scheduledPermanentSpectrumData b hb T hbT front update node initial initialAtoms
      P C hP hf hinitial hnode).layerSpin m i =
        ((scheduledAbsoluteLayerBlock T front update node initial m).get i).2 := rfl

end GapFamily.Construction
