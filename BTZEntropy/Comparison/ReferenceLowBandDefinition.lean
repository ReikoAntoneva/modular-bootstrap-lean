import BTZEntropy.Comparison.ReferenceLowBandMass
import BTZEntropy.Comparison.ReferenceTestDefinition

/-! The exact low-energy correction between the full integer cone and a
fixed leading-reference cutoff. The actual vacuum numerator retains its
zero-energy cancellation in every integrability statement. -/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace BTZEntropy.Comparison

/-- The omitted part of one actual integer-spin row. -/
def lowLeadingRowTest (a T : ℝ) (f : ℝ → ℝ) (j : ℤ) : ℝ :=
  ∫ u in Ioo |(j : ℝ)| T, vacuumLeading a u j * f u ∂referenceMeasure j

/-- The omitted low-energy band, retaining all integer spins. -/
def lowLeadingTest (a T : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑' j : ℤ, lowLeadingRowTest a T f j

/-- The omitted band with the same complete primary descendant modules as
the actual smooth observable. -/
def lowLeadingSmoothCount (φ : SmoothKernel) (a T E : ℝ) : ℝ :=
  lowLeadingTest a T (fullPrimaryDescendantTest φ E)

theorem lowLeadingRowTest_summable (a T : ℝ) (f : ℝ → ℝ) :
    Summable (lowLeadingRowTest a T f) := by
  apply summable_of_hasFiniteSupport
  apply hasFiniteSupport_of_spin_cutoff T
  intro j hj
  simp [lowLeadingRowTest, Ioo_eq_empty_of_le hj]

/-- Compact tests are genuinely integrable even on the complete scalar row,
where the reference measure alone has infinite mass near zero. -/
theorem integrableOn_fullConeLeadingTest {a X : ℝ} (ha : 2 ≤ a)
    (f : ℝ → ℝ) (hf : Continuous f) (hzero : ∀ u, X ≤ u → f u = 0) (j : ℤ) :
    IntegrableOn (fun u => vacuumLeading a u j * f u)
      (Ioi |(j : ℝ)|) (referenceMeasure j) := by
  have hi := (integrableOn_vacuumLeading_lowBand (T := X) ha j).mul_continuousOn_of_subset
    hf.continuousOn measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  apply hi.of_forall_sdiff_eq_zero measurableSet_Ioi
  intro u hu
  have huX : X ≤ u := le_of_not_gt (fun h => hu.2 ⟨hu.1, h⟩)
  rw [hzero u huX, mul_zero]

/-- Exact row splitting uses the ordinary integral, including spin zero. -/
theorem leadingRowTest_zero_eq_low_add_cutoff {a T X : ℝ}
    (ha : 2 ≤ a) (f : ℝ → ℝ) (hf : Continuous f)
    (hzero : ∀ u, X ≤ u → f u = 0) (j : ℤ) :
    leadingRowTest a 0 f j = lowLeadingRowTest a T f j + leadingRowTest a T f j := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_fullConeLeadingTest ha f hf hzero j) (le_max_right T |(j : ℝ)|)
  rw [intervalIntegral.integral_of_le (le_max_right T |(j : ℝ)|),
    integral_Ioc_eq_integral_Ioo] at h
  have hband : Ioo |(j : ℝ)| (max T |(j : ℝ)|) = Ioo |(j : ℝ)| T := by
    by_cases hj : T ≤ |(j : ℝ)|
    · simp [max_eq_right hj, Ioo_eq_empty_of_le hj]
    · rw [max_eq_left (le_of_not_ge hj)]
  rw [hband] at h
  simpa only [leadingRowTest, lowLeadingRowTest, max_eq_right (abs_nonneg (j : ℝ))]
    using sub_eq_iff_eq_add.mp h

/-- The complete cone differs from its cutoff by precisely the low band. -/
theorem integerLeadingTest_zero_eq_low_add_cutoff {a T X : ℝ}
    (ha : 2 ≤ a) (f : ℝ → ℝ) (hf : Continuous f)
    (hzero : ∀ u, X ≤ u → f u = 0) :
    integerLeadingTest a 0 f = lowLeadingTest a T f + integerLeadingTest a T f := by
  unfold integerLeadingTest lowLeadingTest
  simp_rw [leadingRowTest_zero_eq_low_add_cutoff (T := T) ha f hf hzero]
  exact (lowLeadingRowTest_summable a T f).tsum_add (leadingRowTest_summable f hzero)

theorem lowLeadingSmoothCount_eq_packet (φ : SmoothKernel) (a T E R : ℝ)
    (N : ℕ) (hR : ∀ v, φ v ≠ 0 → v ≤ R)
    (hN : E + R + 1 / 12 < (N : ℝ)) :
    lowLeadingSmoothCount φ a T E =
      lowLeadingTest a T (primaryDescendantTest φ E (descendantLevelCutoff N)) := by
  apply tsum_congr
  intro j
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [fullPrimaryDescendantTest_eq_packet φ E R u N
    ((abs_nonneg _).trans hu.1.le) hR hN]

/-- Every full descendant row over the complete physical cone is an
ordinary absolutely convergent integral, including its zero-energy end. -/
theorem integrableOn_fullConeLeadingRow (φ : SmoothKernel) {a : ℝ}
    (ha : 2 ≤ a) (E : ℝ) (j : ℤ) :
    IntegrableOn (fun u => vacuumLeading a u j * fullPrimaryDescendantTest φ E u)
      (Ioi |(j : ℝ)|) (referenceMeasure j) := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  have hR' : ∀ v, φ v ≠ 0 → v ≤ R := fun v hv => hR (subset_tsupport φ hv)
  obtain ⟨N, hN⟩ := exists_nat_gt (E + R + 1 / 12)
  have hi := integrableOn_fullConeLeadingTest ha
    (primaryDescendantTest φ E (descendantLevelCutoff N))
    (continuous_primaryDescendantTest φ E _) (X := (N : ℝ))
    (fun u hu => primaryDescendantTest_eq_zero_of_lt φ E R u _ hR' (hN.trans_le hu)) j
  apply hi.congr_fun _ measurableSet_Ioi
  intro u hu
  dsimp only
  rw [fullPrimaryDescendantTest_eq_packet φ E R u N
    ((abs_nonneg _).trans hu.le) hR' hN]

theorem integrableOn_lowLeadingRow (φ : SmoothKernel) {a : ℝ}
    (ha : 2 ≤ a) (T E : ℝ) (j : ℤ) :
    IntegrableOn (fun u => vacuumLeading a u j * fullPrimaryDescendantTest φ E u)
      (Ioo |(j : ℝ)| T) (referenceMeasure j) :=
  (integrableOn_fullConeLeadingRow φ ha E j).mono_set Ioo_subset_Ioi_self

/-- The cutoff identity concerns the complete all-descendant reference;
finite descendant packets appear only inside the proof. -/
theorem integerLeadingSmoothCount_zero_eq_low_add_cutoff (φ : SmoothKernel)
    {a T : ℝ} (ha : 2 ≤ a) (hT : 0 ≤ T) (E : ℝ) :
    integerLeadingSmoothCount φ a 0 E =
      lowLeadingSmoothCount φ a T E + integerLeadingSmoothCount φ a T E := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  have hR' : ∀ v, φ v ≠ 0 → v ≤ R := fun v hv => hR (subset_tsupport φ hv)
  obtain ⟨N, hN⟩ := exists_nat_gt (E + R + 1 / 12)
  rw [integerLeadingSmoothCount_eq_packet φ a 0 E R N le_rfl hR' hN,
    integerLeadingSmoothCount_eq_packet φ a T E R N hT hR' hN,
    lowLeadingSmoothCount_eq_packet φ a T E R N hR' hN]
  exact integerLeadingTest_zero_eq_low_add_cutoff ha _
    (continuous_primaryDescendantTest φ E _) (X := (N : ℝ))
    (fun u hu => primaryDescendantTest_eq_zero_of_lt φ E R u _ hR' (hN.trans_le hu))

theorem integerLeadingSmoothCount_sub_cutoff (φ : SmoothKernel)
    {a T : ℝ} (ha : 2 ≤ a) (hT : 0 ≤ T) (E : ℝ) :
    integerLeadingSmoothCount φ a 0 E - integerLeadingSmoothCount φ a T E =
      lowLeadingSmoothCount φ a T E := by
  rw [integerLeadingSmoothCount_zero_eq_low_add_cutoff φ ha hT E]
  ring

theorem lowLeadingSmoothCount_nonneg (φ : SmoothKernel) {a : ℝ} (ha : 2 ≤ a)
    (T E : ℝ) : 0 ≤ lowLeadingSmoothCount φ a T E := by
  apply tsum_nonneg
  intro j
  apply setIntegral_nonneg measurableSet_Ioo
  intro u hu
  exact mul_nonneg (vacuumLeading_nonneg a u j ha hu.1.le)
    (moduleSmoothCount_nonneg φ (fun n => Nat.cast_nonneg _) _ _)

/-- A bound on the complete module test costs exactly the true low-band
primary mass; no singular measure mass is substituted for it. -/
theorem lowLeadingSmoothCount_le (φ : SmoothKernel) {a T H : ℝ}
    (ha : 2 ≤ a) (_hT : 0 ≤ T) (E : ℝ) (_hH : 0 ≤ H)
    (hbound : ∀ u ∈ Ioo (0 : ℝ) T, fullPrimaryDescendantTest φ E u ≤ H) :
    lowLeadingSmoothCount φ a T E ≤ H * leadingMass a 0 T := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  have hR' : ∀ v, φ v ≠ 0 → v ≤ R := fun v hv => hR (subset_tsupport φ hv)
  obtain ⟨N, hN⟩ := exists_nat_gt (E + R + 1 / 12)
  rw [lowLeadingSmoothCount_eq_packet φ a T E R N hR' hN]
  have hrow (j : ℤ) :
      lowLeadingRowTest a T (primaryDescendantTest φ E (descendantLevelCutoff N)) j ≤
        H * leadingRowMass a 0 T j := by
    have hi := integrableOn_vacuumLeading_lowBand (T := T) ha j
    have hitest := hi.mul_continuousOn_of_subset
      (continuous_primaryDescendantTest φ E (descendantLevelCutoff N)).continuousOn
      measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
    rw [leadingRowMass, max_eq_right (abs_nonneg (j : ℝ)), ← integral_const_mul]
    apply setIntegral_mono_on hitest (hi.const_mul H) measurableSet_Ioo
    intro u hu
    have hu0 : 0 < u := (abs_nonneg _).trans_lt hu.1
    have ht := hbound u ⟨hu0, hu.2⟩
    rw [fullPrimaryDescendantTest_eq_packet φ E R u N hu0.le hR' hN] at ht
    exact (mul_le_mul_of_nonneg_left ht (vacuumLeading_nonneg a u j ha hu.1.le)).trans_eq
      (mul_comm _ _)
  have hsum := (lowLeadingRowTest_summable a T
    (primaryDescendantTest φ E (descendantLevelCutoff N))).tsum_le_tsum hrow
      ((leadingRowMass_summable a 0 T).mul_left H)
  simpa only [lowLeadingTest, leadingMass, tsum_mul_left] using hsum

end BTZEntropy.Comparison
