import BTZEntropy.Comparison.ReferenceMass
import BTZEntropy.Comparison.DensityErrorTest
import BTZEntropy.Comparison.SpectrumTestSmooth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The genuine integer-spin leading reference, tested with the same cylinder
energy and full descendant packet as the actual spectral observable. -/

noncomputable section
open Set MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace BTZEntropy.Comparison

/-- Leading continuum test in one physical integer-spin row. -/
def leadingRowTest (a T : ℝ) (f : ℝ → ℝ) (j : ℤ) : ℝ :=
  ∫ u in Ioi (max T |(j : ℝ)|), vacuumLeading a u j * f u ∂referenceMeasure j

/-- All actual integer spins of the leading reference. -/
def integerLeadingTest (a T : ℝ) (f : ℝ → ℝ) : ℝ := ∑' j : ℤ, leadingRowTest a T f j

/-- The complete primary descendant module as a test of reduced energy. -/
def fullPrimaryDescendantTest (φ : SmoothKernel) (E u : ℝ) : ℝ :=
  moduleSmoothCount φ (fun n => (partitionCount n : ℝ)) (u - 1 / 12) E

/-- The all-descendant, integer-spin leading reference count. Vacuum and
the finite initial packet remain separate in the exact comparison identity. -/
def integerLeadingSmoothCount (φ : SmoothKernel) (a T E : ℝ) : ℝ :=
  integerLeadingTest a T (fullPrimaryDescendantTest φ E)

/-- Its finite descendant packet, used after exact compact-test truncation. -/
def integerLeadingPacketCount (φ : SmoothKernel) (a T E : ℝ)
    (F : Finset (ℕ × ℕ)) : ℝ := integerLeadingTest a T (primaryDescendantTest φ E F)

/-- Nonnegative primary energies share the same finite descendant cutoff. -/
theorem fullPrimaryDescendantTest_eq_packet (φ : SmoothKernel) (E R u : ℝ)
    (N : ℕ) (hu : 0 ≤ u) (hR : ∀ v, φ v ≠ 0 → v ≤ R)
    (hN : E + R + 1 / 12 < (N : ℝ)) :
    fullPrimaryDescendantTest φ E u = primaryDescendantTest φ E (descendantLevelCutoff N) u := by
  unfold fullPrimaryDescendantTest moduleSmoothCount primaryDescendantTest
  apply tsum_eq_sum
  intro l hl
  unfold moduleSmoothTerm
  have hz : φ (u - 1 / 12 + (l.1 : ℝ) + (l.2 : ℝ) - E) = 0 := by
    by_contra hn
    have hb := hR _ hn
    apply hl
    rw [mem_descendantLevelCutoff]
    constructor <;> apply (Nat.cast_le (α := ℝ)).mp
    · linarith [Nat.cast_nonneg (α := ℝ) l.2]
    · linarith [Nat.cast_nonneg (α := ℝ) l.1]
  rw [hz, mul_zero]

/-- Compact energy support turns the open half-line integral into an exact
bounded-band integral, including every opening spin edge. -/
theorem leadingRowTest_eq_bounded (a T X : ℝ) (f : ℝ → ℝ)
    (hf : ∀ u, X ≤ u → f u = 0) (j : ℤ) :
    leadingRowTest a T f j =
      ∫ u in Ioo (max T |(j : ℝ)|) X, vacuumLeading a u j * f u ∂referenceMeasure j := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioo_subset_Ioi_self
  intro u hu
  have huX : X ≤ u := le_of_not_gt (fun h => hu.2 ⟨hu.1, h⟩)
  rw [hf u huX, mul_zero]

/-- The compact leading test is genuinely integrable on its physical row. -/
theorem integrableOn_leadingRowTest {a T X : ℝ} (ha : 2 ≤ a) (hT : 1 ≤ T)
    (f : ℝ → ℝ) (hf : Continuous f) (hzero : ∀ u, X ≤ u → f u = 0) (j : ℤ) :
    IntegrableOn (fun u => vacuumLeading a u j * f u)
      (Ioi (max T |(j : ℝ)|)) (referenceMeasure j) := by
  have hi := (integrable_leadingRow (X := X) j ha hT).mul_continuousOn_of_subset
    hf.continuousOn measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  apply hi.of_forall_sdiff_eq_zero measurableSet_Ioi
  intro u hu
  have huX : X ≤ u := le_of_not_gt (fun h => hu.2 ⟨hu.1, h⟩)
  rw [hzero u huX, mul_zero]

/-- A compact test has no contribution from spins above its energy support. -/
theorem leadingRowTest_eq_zero {a T X : ℝ} (f : ℝ → ℝ)
    (hf : ∀ u, X ≤ u → f u = 0) (j : ℤ) (hj : X ≤ |(j : ℝ)|) :
    leadingRowTest a T f j = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro u hu
  rw [hf u (hj.trans ((le_max_right _ _).trans hu.le)), mul_zero]

/-- Any row family with a finite physical energy support has finite support
as an integer-spin sum. -/
theorem hasFiniteSupport_of_spin_cutoff {F : ℤ → ℝ} (X : ℝ)
    (hF : ∀ j : ℤ, X ≤ |(j : ℝ)| → F j = 0) : Function.HasFiniteSupport F := by
  classical
  apply (Finset.finite_toSet (Finset.Icc (-⌈X⌉) ⌈X⌉)).subset
  intro j hj
  have habs : |(j : ℝ)| < X := lt_of_not_ge (fun h => hj (hF j h))
  have hceil := Int.le_ceil X
  simp only [Finset.mem_coe, Finset.mem_Icc]
  constructor
  · have h := (abs_lt.mp habs).1
    exact_mod_cast (show -(⌈X⌉ : ℝ) ≤ (j : ℝ) by linarith)
  · have h := (abs_lt.mp habs).2
    exact_mod_cast (show (j : ℝ) ≤ (⌈X⌉ : ℝ) by linarith)

theorem leadingRowTest_summable {a T X : ℝ} (f : ℝ → ℝ)
    (hf : ∀ u, X ≤ u → f u = 0) : Summable (leadingRowTest a T f) :=
  summable_of_hasFiniteSupport
    (hasFiniteSupport_of_spin_cutoff X (leadingRowTest_eq_zero f hf))

/-- Exact descendant truncation applies to the actual leading reference too. -/
theorem integerLeadingSmoothCount_eq_packet (φ : SmoothKernel) (a T E R : ℝ)
    (N : ℕ) (hT : 0 ≤ T) (hR : ∀ v, φ v ≠ 0 → v ≤ R)
    (hN : E + R + 1 / 12 < (N : ℝ)) :
    integerLeadingSmoothCount φ a T E =
      integerLeadingPacketCount φ a T E (descendantLevelCutoff N) := by
  apply tsum_congr
  intro j
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [fullPrimaryDescendantTest_eq_packet φ E R u N
    (hT.trans ((le_max_left _ _).trans hu.le)) hR hN]

/-- Every physical row of the full descendant reference has an ordinary
absolutely convergent integral, as witnessed by its exact finite packet. -/
theorem integrableOn_fullLeadingRow {a T : ℝ} (ha : 2 ≤ a) (hT : 1 ≤ T)
    (φ : SmoothKernel) (E : ℝ) (j : ℤ) :
    IntegrableOn (fun u => vacuumLeading a u j * fullPrimaryDescendantTest φ E u)
      (Ioi (max T |(j : ℝ)|)) (referenceMeasure j) := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  have hR' : ∀ v, φ v ≠ 0 → v ≤ R := fun v hv => hR (subset_tsupport φ hv)
  obtain ⟨N, hN⟩ := exists_nat_gt (E + R + 1 / 12)
  have hi := integrableOn_leadingRowTest ha hT
    (primaryDescendantTest φ E (descendantLevelCutoff N))
    (continuous_primaryDescendantTest φ E _)
    (X := (N : ℝ))
    (fun u hu => primaryDescendantTest_eq_zero_of_lt φ E R u _ hR' (hN.trans_le hu)) j
  apply hi.congr_fun _ measurableSet_Ioi
  intro u hu
  dsimp only
  rw [fullPrimaryDescendantTest_eq_packet φ E R u N
    (by linarith [(le_max_left T |(j : ℝ)|).trans hu.le]) hR' hN]

/-- The complete reference has only finitely many contributing spin rows in
each compact spectral window; its integer-spin `tsum` is a genuine sum. -/
theorem fullLeadingRow_summable (φ : SmoothKernel) (a T E : ℝ) (hT : 0 ≤ T) :
    Summable (leadingRowTest a T (fullPrimaryDescendantTest φ E)) := by
  obtain ⟨R, hR⟩ := φ.compactSupport.bddAbove
  have hR' : ∀ v, φ v ≠ 0 → v ≤ R := fun v hv => hR (subset_tsupport φ hv)
  obtain ⟨N, hN⟩ := exists_nat_gt (E + R + 1 / 12)
  apply (leadingRowTest_summable (a := a) (T := T)
    (primaryDescendantTest φ E (descendantLevelCutoff N)) (X := (N : ℝ))
    (fun u hu => primaryDescendantTest_eq_zero_of_lt φ E R u _ hR' (hN.trans_le hu))).congr
  intro j
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [fullPrimaryDescendantTest_eq_packet φ E R u N
    (hT.trans ((le_max_left _ _).trans hu.le)) hR' hN]

end BTZEntropy.Comparison
