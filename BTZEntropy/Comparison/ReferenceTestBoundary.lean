import BTZEntropy.Comparison.ReferenceTestDefinition
import BTZEntropy.Construction.FixedFamilyData

/-! The boundary band between the fixed leading-reference cutoff and the
actual initial row fronts. The band is retained in the exact comparison,
and is bounded uniformly by the finite leading-reference mass. -/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace BTZEntropy.Comparison

/-- The finite interval omitted when the actual tail starts beyond the
uniform reference cutoff. -/
def frontBoundaryRowTest (a T : ℝ) (front : ℤ → ℝ) (f : ℝ → ℝ) (j : ℤ) : ℝ :=
  ∫ u in Ioo (max T |(j : ℝ)|) (front j),
    vacuumLeading a u j * f u ∂referenceMeasure j

/-- The boundary correction contains every actual integer-spin row. -/
def frontBoundaryTest (a T : ℝ) (front : ℤ → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑' j : ℤ, frontBoundaryRowTest a T front f j

/-- The reference tail starting at the actual front of one row. -/
def frontTailRowTest (a : ℝ) (front : ℤ → ℝ) (f : ℝ → ℝ) (j : ℤ) : ℝ :=
  ∫ u in Ioi (front j), vacuumLeading a u j * f u ∂referenceMeasure j

theorem leadingRowTest_eq_boundary_add_tail {a T X : ℝ}
    (ha : 2 ≤ a) (hT : 1 ≤ T) (front : ℤ → ℝ)
    (hfront : ∀ j : ℤ, max T |(j : ℝ)| ≤ front j)
    (f : ℝ → ℝ) (hf : Continuous f) (hzero : ∀ u, X ≤ u → f u = 0) (j : ℤ) :
    leadingRowTest a T f j = frontBoundaryRowTest a T front f j +
      frontTailRowTest a front f j := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_leadingRowTest ha hT f hf hzero j) (hfront j)
  rw [intervalIntegral.integral_of_le (hfront j), integral_Ioc_eq_integral_Ioo] at h
  exact sub_eq_iff_eq_add.mp h

theorem frontBoundaryRowTest_eq_zero {a T X : ℝ}
    (front : ℤ → ℝ) (f : ℝ → ℝ) (hzero : ∀ u, X ≤ u → f u = 0)
    (j : ℤ) (hj : X ≤ |(j : ℝ)|) :
    frontBoundaryRowTest a T front f j = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro u hu
  rw [hzero u (hj.trans ((le_max_right _ _).trans hu.1.le)), mul_zero]

theorem frontTailRowTest_eq_zero {a T X : ℝ}
    (front : ℤ → ℝ) (hfront : ∀ j : ℤ, max T |(j : ℝ)| ≤ front j)
    (f : ℝ → ℝ) (hzero : ∀ u, X ≤ u → f u = 0)
    (j : ℤ) (hj : X ≤ |(j : ℝ)|) :
    frontTailRowTest a front f j = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro u hu
  rw [hzero u (hj.trans (((le_max_right _ _).trans (hfront j)).trans hu.le)), mul_zero]

theorem frontBoundaryRowTest_summable {a T X : ℝ}
    (front : ℤ → ℝ) (f : ℝ → ℝ) (hzero : ∀ u, X ≤ u → f u = 0) :
    Summable (frontBoundaryRowTest a T front f) :=
  summable_of_hasFiniteSupport (hasFiniteSupport_of_spin_cutoff X
    (frontBoundaryRowTest_eq_zero front f hzero))

theorem frontTailRowTest_summable {a T X : ℝ}
    (front : ℤ → ℝ) (hfront : ∀ j : ℤ, max T |(j : ℝ)| ≤ front j)
    (f : ℝ → ℝ) (hzero : ∀ u, X ≤ u → f u = 0) :
    Summable (frontTailRowTest a front f) :=
  summable_of_hasFiniteSupport (hasFiniteSupport_of_spin_cutoff X
    (frontTailRowTest_eq_zero front hfront f hzero))

/-- Exact separation of the uniform leading reference into the initial
boundary band and the reference traversed by the actual tail. -/
theorem integerLeadingTest_eq_boundary_add_tail {a T X : ℝ}
    (ha : 2 ≤ a) (hT : 1 ≤ T) (front : ℤ → ℝ)
    (hfront : ∀ j : ℤ, max T |(j : ℝ)| ≤ front j)
    (f : ℝ → ℝ) (hf : Continuous f) (hzero : ∀ u, X ≤ u → f u = 0) :
    integerLeadingTest a T f = frontBoundaryTest a T front f +
      ∑' j : ℤ, frontTailRowTest a front f j := by
  unfold integerLeadingTest frontBoundaryTest
  simp_rw [leadingRowTest_eq_boundary_add_tail ha hT front hfront f hf hzero]
  exact (frontBoundaryRowTest_summable front f hzero).tsum_add
    (frontTailRowTest_summable front hfront f hzero)

/-- A uniform bound on the front alone makes the boundary spin sum finite,
even without any support assumption on the test. -/
theorem frontBoundaryRowTest_summable_of_front_le {a T X : ℝ}
    (front : ℤ → ℝ) (hfront : ∀ j, front j ≤ max X |(j : ℝ)|) (f : ℝ → ℝ) :
    Summable (frontBoundaryRowTest a T front f) := by
  apply summable_of_hasFiniteSupport
  apply hasFiniteSupport_of_spin_cutoff X
  intro j hj
  have hle : front j ≤ max T |(j : ℝ)| := by
    exact (hfront j).trans (by rw [max_eq_right hj]; exact le_max_right _ _)
  simp [frontBoundaryRowTest, Ioo_eq_empty_of_le hle]

theorem frontBoundaryRowTest_nonneg {a T : ℝ} (ha : 2 ≤ a)
    (front : ℤ → ℝ) (f : ℝ → ℝ) (hf : ∀ u, T ≤ u → 0 ≤ f u) (j : ℤ) :
    0 ≤ frontBoundaryRowTest a T front f j := by
  apply setIntegral_nonneg measurableSet_Ioo
  intro u hu
  exact mul_nonneg
    (vacuumLeading_nonneg a u j ha ((le_max_right _ _).trans hu.1.le))
    (hf u ((le_max_left _ _).trans hu.1.le))

theorem frontBoundaryTest_nonneg {a T : ℝ} (ha : 2 ≤ a)
    (front : ℤ → ℝ) (f : ℝ → ℝ) (hf : ∀ u, T ≤ u → 0 ≤ f u) :
    0 ≤ frontBoundaryTest a T front f :=
  tsum_nonneg (frontBoundaryRowTest_nonneg ha front f hf)

/-- Each boundary row is controlled by the same bounded leading-reference
mass, including intervals touching the physical spin edge. -/
theorem frontBoundaryRowTest_le {a T X H : ℝ} (j : ℤ)
    (ha : 2 ≤ a) (hT : 1 ≤ T) (hH : 0 ≤ H)
    (front : ℤ → ℝ) (hfront : front j ≤ max X |(j : ℝ)|)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hbound : ∀ u ∈ Ioo (max T |(j : ℝ)|) X, f u ≤ H) :
    frontBoundaryRowTest a T front f j ≤ H * leadingRowMass a T X j := by
  have hsub : Ioo (max T |(j : ℝ)|) (front j) ⊆
      Ioo (max T |(j : ℝ)|) X := by
    intro u hu
    refine ⟨hu.1, ?_⟩
    exact (lt_max_iff.mp (hu.2.trans_le hfront)).resolve_right
      (not_lt.mpr ((le_max_right _ _).trans hu.1.le))
  have hi := integrable_leadingRow (X := X) j ha hT
  have hif := hi.mul_continuousOn_of_subset hf.continuousOn
    measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have hiH : IntegrableOn (fun u => H * vacuumLeading a u j)
      (Ioo (max T |(j : ℝ)|) X) (referenceMeasure j) := hi.const_mul H
  calc
    _ ≤ ∫ u in Ioo (max T |(j : ℝ)|) (front j),
        H * vacuumLeading a u j ∂referenceMeasure j := by
      apply setIntegral_mono_on (hif.mono_set hsub)
        (hiH.mono_set hsub) measurableSet_Ioo
      intro u hu
      rw [mul_comm H]
      exact mul_le_mul_of_nonneg_left (hbound u (hsub hu))
        (vacuumLeading_nonneg a u j ha ((le_max_right _ _).trans hu.1.le))
    _ ≤ ∫ u in Ioo (max T |(j : ℝ)|) X,
        H * vacuumLeading a u j ∂referenceMeasure j := by
      apply setIntegral_mono_set hiH ?_
        (Filter.Eventually.of_forall fun u hu => hsub hu)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact mul_nonneg hH
        (vacuumLeading_nonneg a u j ha ((le_max_right _ _).trans hu.1.le))
    _ = _ := integral_const_mul _ _

/-- The complete boundary correction costs only the leading mass up to
the fixed front bound, multiplied by the test's size on that band. -/
theorem frontBoundaryTest_le {a T X H : ℝ}
    (ha : 2 ≤ a) (hT : 1 ≤ T) (hH : 0 ≤ H)
    (front : ℤ → ℝ) (hfront : ∀ j, front j ≤ max X |(j : ℝ)|)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hbound : ∀ u ∈ Ioo T X, f u ≤ H) :
    frontBoundaryTest a T front f ≤ H * leadingMass a T X := by
  calc
    _ ≤ ∑' j : ℤ, H * leadingRowMass a T X j := by
      apply (frontBoundaryRowTest_summable_of_front_le front hfront f).tsum_le_tsum
        (fun j => frontBoundaryRowTest_le j ha hT hH front (hfront j) f hf
          (fun u hu => hbound u ⟨(le_max_left _ _).trans_lt hu.1, hu.2⟩))
        ((leadingRowMass_summable a T X).mul_left H)
    _ = _ := tsum_mul_left

theorem frontBoundaryTest_le_exp {a T X H : ℝ}
    (ha : 2 ≤ a) (hT : 1 ≤ T) (hH : 0 ≤ H) (hX : 0 ≤ X)
    (front : ℤ → ℝ) (hfront : ∀ j, front j ≤ max X |(j : ℝ)|)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hbound : ∀ u ∈ Ioo T X, f u ≤ H) :
    frontBoundaryTest a T front f ≤
      6 * H * (1 + X) ^ 2 * exp (4 * π * sqrt (a * X)) := by
  calc
    _ ≤ H * leadingMass a T X := frontBoundaryTest_le ha hT hH front hfront f hf hbound
    _ ≤ H * (6 * (1 + X) ^ 2 * exp (4 * π * sqrt (a * X))) :=
      mul_le_mul_of_nonneg_left (leadingMass_le ha hT hX) hH
    _ = _ := by ring

open BTZEntropy.Construction GapFamily

/-- The fixed family's actual initial fronts lie in the same fixed energy
band, uniformly in the charge, marker, and selector. -/
theorem fixedFamily_initial_front_le {B : ℝ} {g : FixedFamilyGeometry B}
    {a : ℝ} {δ : ℝ} (d : FixedFamilyDatum g a δ) (j : ℤ) :
    d.initialState.front j ≤ max (g.upper + 1) |(j : ℝ)| := by
  have hstart : (g.start : ℝ) + 1 ≤ g.upper + 1 := by
    linarith [g.start_le_radius, g.radius_le_upper]
  apply (d.initial_front_upper j).trans
  exact max_le (le_max_left _ _)
    (max_le (hstart.trans (le_max_left _ _)) (le_max_right _ _))

theorem fixedFamily_integerLeadingTest_eq_boundary_add_tail
    {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ X : ℝ}
    (d : FixedFamilyDatum g a δ) (f : ℝ → ℝ) (hf : Continuous f)
    (hzero : ∀ u, X ≤ u → f u = 0) :
    integerLeadingTest (shift (gapFamilyCharge a)) g.start f =
      frontBoundaryTest (shift (gapFamilyCharge a)) g.start d.initialState.front f +
      ∑' j : ℤ, frontTailRowTest (shift (gapFamilyCharge a)) d.initialState.front f j :=
  integerLeadingTest_eq_boundary_add_tail (by linarith [d.charge_large])
    (by exact_mod_cast g.start_pos) d.initialState.front d.initial_front f hf hzero

/-- The same boundary estimate applies to every actual fixed-family datum;
the cutoff is determined by its common geometry alone. -/
theorem fixedFamily_frontBoundaryTest_le
    {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ H : ℝ}
    (d : FixedFamilyDatum g a δ) (hH : 0 ≤ H) (f : ℝ → ℝ) (hf : Continuous f)
    (hbound : ∀ u ∈ Ioo (g.start : ℝ) (g.upper + 1), f u ≤ H) :
    frontBoundaryTest (shift (gapFamilyCharge a)) g.start d.initialState.front f ≤
      H * leadingMass (shift (gapFamilyCharge a)) g.start (g.upper + 1) :=
  frontBoundaryTest_le (by linarith [d.charge_large]) (by exact_mod_cast g.start_pos)
    hH d.initialState.front (fixedFamily_initial_front_le d) f hf hbound

theorem fixedFamily_frontBoundaryTest_le_exp
    {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ H : ℝ}
    (d : FixedFamilyDatum g a δ) (hH : 0 ≤ H) (f : ℝ → ℝ) (hf : Continuous f)
    (hbound : ∀ u ∈ Ioo (g.start : ℝ) (g.upper + 1), f u ≤ H) :
    frontBoundaryTest (shift (gapFamilyCharge a)) g.start d.initialState.front f ≤
      6 * H * (g.upper + 2) ^ 2 *
        exp (4 * π * sqrt (shift (gapFamilyCharge a) * (g.upper + 1))) := by
  have h := frontBoundaryTest_le_exp (a := shift (gapFamilyCharge a))
    (T := g.start) (X := g.upper + 1) (by linarith [d.charge_large])
    (by exact_mod_cast g.start_pos) hH (by linarith [g.upper_nonneg])
    d.initialState.front (fixedFamily_initial_front_le d) f hf hbound
  convert h using 1
  ring

end BTZEntropy.Comparison
