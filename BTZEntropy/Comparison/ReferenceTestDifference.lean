import BTZEntropy.Comparison.ReferenceTestAssembly

/-! The exact smooth-count comparison on the actual fixed-cutoff spectrum.
Quadrature, current-density, and initial-front errors remain distinct. -/

noncomputable section
open Set MeasureTheory Real
open GapFamily GapFamily.Analytic GapFamily.Construction
open BTZEntropy.Construction
open scoped BigOperators Classical

namespace BTZEntropy.Comparison

variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
  (d : RealTailLocalData a U T degree) (initial : FiniteRepairState)

/-- The actual unit-node test minus its own current continuum cell. -/
def scheduledQuadratureDifference (f : ℝ → ℝ) (p : LayerSlotIndex T) : ℝ :=
  scheduledCellTest d initial (fun q => f q.1) p - scheduledCurrentCellTest d initial f p

/-- The actual current continuum cell minus the leading reference on the
same geometric interval. -/
def scheduledDensityDifference (f : ℝ → ℝ) (p : LayerSlotIndex T) : ℝ :=
  scheduledCurrentCellTest d initial f p - scheduledLeadingCellTest d initial f p

theorem scheduledQuadratureDifference_active (f : ℝ → ℝ) (p : d.ActiveSlot initial) :
    scheduledQuadratureDifference d initial f p.val =
      (∑ i : Fin (d.activeCell initial p).count, f ((d.activeCell initial p).node i)) -
      ∫ u in Ioo ((d.slotPreState initial p.val).front p.val.row)
        (d.activeCell initial p).right,
        (d.slotPreState initial p.val).numerator p.val.row u * f u
          ∂referenceMeasure p.val.row := by
  rw [scheduledQuadratureDifference, scheduledCellTest_active,
    scheduledCurrentCellTest_active]

/-- The density discrepancy is the ordinary integral of the true preceding
state's error, precisely the quantity controlled by the vacuum envelope. -/
theorem scheduledDensityDifference_active (ha : 2 ≤ a) (hT : (1 : ℝ) ≤ T)
    (f : ℝ → ℝ) (hf : Continuous f) (p : d.ActiveSlot initial) :
    scheduledDensityDifference d initial f p.val =
      ∫ u in Ioo ((d.slotPreState initial p.val).front p.val.row)
        (d.activeCell initial p).right,
        ((d.slotPreState initial p.val).numerator p.val.row u - vacuumLeading a u p.val.row) *
          f u ∂referenceMeasure p.val.row := by
  have hL : 1 ≤ (d.slotPreState initial p.val).front p.val.row :=
    hT.trans ((by exact_mod_cast p.property.layer : (T : ℝ) ≤ p.val.layer).trans
      p.property.front_lower)
  have hlead := integrable_leadingRow
    (T := (d.slotPreState initial p.val).front p.val.row)
    (X := (d.activeCell initial p).right) p.val.row ha hL
  rw [max_eq_left p.property.physical] at hlead
  have hleadTest := hlead.mul_continuousOn_of_subset hf.continuousOn
    measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have hcurrentTest := (d.activeCell initial p).density_integrable.mul_continuousOn_of_subset
    hf.continuousOn measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  rw [scheduledDensityDifference, scheduledCurrentCellTest_active,
    scheduledLeadingCellTest_active, ← integral_sub hcurrentTest hleadTest]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by ring)

theorem scheduledQuadratureDifference_invalid (f : ℝ → ℝ) (p : LayerSlotIndex T)
    (hp : ¬RealTailStepValid a T (d.slotPreState initial p) p.layer p.row) :
    scheduledQuadratureDifference d initial f p = 0 := by
  rw [scheduledQuadratureDifference, scheduledCurrentCellTest_invalid d initial f p hp]
  unfold scheduledCellTest
  rw [dite_eq_right hp, sub_self]

theorem scheduledDensityDifference_invalid (f : ℝ → ℝ) (p : LayerSlotIndex T)
    (hp : ¬RealTailStepValid a T (d.slotPreState initial p) p.layer p.row) :
    scheduledDensityDifference d initial f p = 0 := by
  rw [scheduledDensityDifference, scheduledCurrentCellTest_invalid d initial f p hp,
    scheduledLeadingCellTest_invalid d initial f p hp, sub_self]

/-- The same actual fixed-family spectrum differs from the full
integer-spin leading reference by these exact finite contributions. In
particular, the initial-front boundary band has not been silently omitted. -/
theorem fixedFamily_smoothCount_sub_integerLeading
    {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}
    (D : FixedFamilyDatum g a δ) (φ : SmoothKernel) (E R : ℝ) (N k : ℕ)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hNv : E + R + gapFamilyCharge a / 12 < (N : ℝ))
    (hNp : E + R + 1 / 12 < (N : ℝ))
    (hk : E + R + 1 / 12 < ((g.start + k : ℕ) : ℝ)) :
    smoothCount φ (gapFamilyCharge a) D.spectrum E -
      integerLeadingSmoothCount φ (shift (gapFamilyCharge a)) g.start E =
      vacuumFiniteLevelCount φ (gapFamilyCharge a) E (descendantLevelCutoff N) +
      primaryDescendantTest φ E (descendantLevelCutoff N) δ +
      (D.initialState.nodes.map (fun p => primaryDescendantTest φ E (descendantLevelCutoff N) p.1)).sum -
      frontBoundaryTest (shift (gapFamilyCharge a)) g.start D.initialState.front
        (primaryDescendantTest φ E (descendantLevelCutoff N)) +
      ∑ m ∈ Finset.range k, ∑ q : Fin (layerSlots (g.start + m)).length,
        (scheduledQuadratureDifference D.tail D.initialState
            (primaryDescendantTest φ E (descendantLevelCutoff N)) ⟨m, q⟩ +
          scheduledDensityDifference D.tail D.initialState
            (primaryDescendantTest φ E (descendantLevelCutoff N)) ⟨m, q⟩) := by
  have hs := smoothCount_eq_initial_add_cell D.tail D.initialState δ D.marker_nonneg
    D.marker_lt_start.le D.initial_nodes_bounds φ (gapFamilyCharge a) E R N k hR hNv hNp hk
  change smoothCount φ (gapFamilyCharge a) D.spectrum E = _ at hs
  rw [hs, integerLeadingSmoothCount_eq_packet φ _ _ E R N
    (by exact_mod_cast (Nat.zero_le g.start)) hR hNp, integerLeadingPacketCount,
    fixedFamily_integerLeadingTest_eq_boundary_add_cell D
      (primaryDescendantTest φ E (descendantLevelCutoff N))
      (continuous_primaryDescendantTest φ E _) (X := ((g.start + k : ℕ) : ℝ))
      (fun u hu => primaryDescendantTest_eq_zero_of_lt φ E R u _ hR (hk.trans_le hu))
      k le_rfl]
  have hcancel (p : LayerSlotIndex g.start) :
      scheduledQuadratureDifference D.tail D.initialState
          (primaryDescendantTest φ E (descendantLevelCutoff N)) p +
        scheduledDensityDifference D.tail D.initialState
          (primaryDescendantTest φ E (descendantLevelCutoff N)) p =
      scheduledCellTest D.tail D.initialState
          (fun q => primaryDescendantTest φ E (descendantLevelCutoff N) q.1) p -
        scheduledLeadingCellTest D.tail D.initialState
          (primaryDescendantTest φ E (descendantLevelCutoff N)) p := by
    unfold scheduledQuadratureDifference scheduledDensityDifference
    ring
  simp_rw [hcancel, Finset.sum_sub_distrib]
  ring

end BTZEntropy.Comparison
