import GapFamily.Construction.RealTailRecurrence
import GapFamily.Construction.RealTailRepairBudget
import GapFamily.Construction.CanonicalTailParameterConstant

/-! The local real-parameter recursion contract is discharged by the actual
canonical cells and their proved exterior estimates. -/

noncomputable section
open Set MeasureTheory Real Filter
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A ray-dependent threshold; the moment multiplier is fixed beforehand. -/
def realCanonicalTailThreshold {t : ℝ} (ht : 0 < t) : ℕ :=
  max 100 (realTailCellThreshold ht canonicalTailMomentMultiplier_pos)

theorem realCanonicalTailThreshold_spec {t : ℝ} (ht : 0 < t) {a : ℝ}
    (ha : (realCanonicalTailThreshold ht : ℝ) ≤ a) :
    100 ≤ a ∧ (realTailCellThreshold ht canonicalTailMomentMultiplier_pos : ℝ) ≤ a := by
  have h100 : (100 : ℝ) ≤ (realCanonicalTailThreshold ht : ℝ) := by
    exact_mod_cast (le_max_left 100
      (realTailCellThreshold ht canonicalTailMomentMultiplier_pos))
  have hcell : (realTailCellThreshold ht canonicalTailMomentMultiplier_pos : ℝ) ≤
      (realCanonicalTailThreshold ht : ℝ) := by
    exact_mod_cast (le_max_right 100
      (realTailCellThreshold ht canonicalTailMomentMultiplier_pos))
  exact ⟨h100.trans ha, hcell.trans ha⟩

/-- Every valid local slot has its actual moment-matched cell and the full
canonical exterior repair budget, for arbitrary real charge and cutoff. -/
def realTailLocalData {t : ℝ} (ht : 0 < t) {a U : ℝ} {T : ℕ}
    (ha : (realCanonicalTailThreshold ht : ℝ) ≤ a) (hT : 1 ≤ T)
    (hray : t * a ≤ (T : ℝ)) (hU₀ : 0 ≤ U) (hUa : U ≤ a) :
    RealTailLocalData a U T (realTailMomentDegree canonicalTailMomentMultiplier a) where
  cutoff_nonneg := hU₀
  cell state m J h :=
    selectedRealTailCell ht canonicalTailMomentMultiplier_pos
      (realCanonicalTailThreshold_spec ht ha).2
      (hray.trans ((by exact_mod_cast h.layer : (T : ℝ) ≤ m).trans h.front_lower))
      h.front_lower h.front_upper h.physical
      (state.integrableOn_numerator h.thermal J (state.front J) (state.front J + 1))
      h.envelope
  error state m J h j E hj hE := by
    apply TailCell.real_exteriorNumerator_le_slotBudget _
      (realCanonicalTailThreshold_spec ht ha).1
      ((by exact_mod_cast hT.trans h.layer : (1 : ℝ) ≤ m).trans h.front_lower)
      h.front_upper h.physical hU₀ hUa h.envelope j E hj hE.le
      (canonicalTailChargeThreshold_real_spec a (realCanonicalTailThreshold_spec ht ha).1)
      canonicalTailMomentMultiplier_budget

/-- The threshold is uniform in the initial cutoff and all subsequent layers. -/
theorem eventually_nonempty_realTailLocalData {t : ℝ} (ht : 0 < t) :
    ∀ᶠ a : ℝ in atTop, ∀ U : ℝ, 0 ≤ U → U ≤ a →
      ∀ T : ℕ, 1 ≤ T → t * a ≤ (T : ℝ) →
      Nonempty (RealTailLocalData a U T
        (realTailMomentDegree canonicalTailMomentMultiplier a)) := by
  filter_upwards [eventually_ge_atTop (realCanonicalTailThreshold ht : ℝ)] with a ha
  intro U hU₀ hUa T hT hray
  exact ⟨realTailLocalData ht ha hT hray hU₀ hUa⟩

end GapFamily.Construction
