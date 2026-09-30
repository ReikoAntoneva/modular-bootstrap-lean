import BTZEntropy.Construction.FixedFamilyData
import GapFamily.Construction.FixedCutoffReferenceDensityMass

/-!
# Explicit geometry for a fixed cutoff

Every length and the initial tail layer are chosen before the central
charge or marker. The enlarged clearing cutoff is an integer, so the
initial row radius is also the integer starting layer of the tail.
-/

noncomputable section

open Real
open GapFamily.Construction

namespace BTZEntropy.Construction

def fixedFamilyClearingNat (B : ℝ) : ℕ :=
  max ⌈B⌉₊ fixedCutoffReferenceBandThreshold

theorem fixedFamilyClearingNat_hundred (B : ℝ) :
    100 ≤ fixedFamilyClearingNat B :=
  fixedCutoffReferenceBandThreshold_ge_hundred.trans (le_max_right _ _)

theorem le_fixedFamilyClearingNat (B : ℝ) : B ≤ (fixedFamilyClearingNat B : ℝ) := by
  exact (Nat.le_ceil B).trans (by exact_mod_cast (le_max_left ⌈B⌉₊ fixedCutoffReferenceBandThreshold))

def fixedFamilyUpper (B : ℝ) : ℝ :=
  16 * (fixedCutoffReferenceRadius : ℝ) * (fixedFamilyClearingNat B : ℝ) +
    4 * fixedCutoffReferenceNegativeExponent ^ 2 * (fixedFamilyClearingNat B : ℝ) +
    16 + 2 / (π ^ 4 / 625) + 1

private theorem fixedFamilyUpper_bounds (B : ℝ) :
    16 ≤ fixedFamilyUpper B ∧ 2 / (π ^ 4 / 625) < fixedFamilyUpper B ∧
    16 * (fixedCutoffReferenceRadius : ℝ) * (fixedFamilyClearingNat B : ℝ) ≤
      fixedFamilyUpper B ∧
    4 * fixedCutoffReferenceNegativeExponent ^ 2 * (fixedFamilyClearingNat B : ℝ) ≤
      fixedFamilyUpper B := by
  have hR : 0 ≤ 16 * (fixedCutoffReferenceRadius : ℝ) * (fixedFamilyClearingNat B : ℝ) := by
    positivity
  have hN : 0 ≤ 4 * fixedCutoffReferenceNegativeExponent ^ 2 *
      (fixedFamilyClearingNat B : ℝ) := by positivity
  have hP : 0 < 2 / (π ^ 4 / 625) := by positivity
  unfold fixedFamilyUpper
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Explicit geometry, valid in particular for every positive requested
cutoff. The charge and marker do not occur in its definition. -/
def fixedFamilyGeometry (B : ℝ) : FixedFamilyGeometry B where
  clearing := fixedFamilyClearingNat B
  radius := (fixedCutoffReferenceRadius * fixedFamilyClearingNat B : ℕ)
  upper := fixedFamilyUpper B
  start := fixedCutoffReferenceRadius * fixedFamilyClearingNat B
  cutoff_le := le_fixedFamilyClearingNat B
  cutoff_lt_start := by
    have hC : (100 : ℝ) ≤ fixedFamilyClearingNat B := by
      exact_mod_cast fixedFamilyClearingNat_hundred B
    have hR : (6 : ℝ) < fixedCutoffReferenceRadius := by
      exact_mod_cast fixedCutoffReferenceRadius_gt_six
    have hBC := le_fixedFamilyClearingNat B
    push_cast
    nlinarith
  start_pos := by
    have hC := fixedFamilyClearingNat_hundred B
    have hR := fixedCutoffReferenceRadius_gt_six
    nlinarith
  radius_nonneg := Nat.cast_nonneg _
  start_le_radius := le_rfl
  radius_le_upper := by
    have h := (fixedFamilyUpper_bounds B).2.2.1
    have hR : 0 ≤ (fixedCutoffReferenceRadius : ℝ) * (fixedFamilyClearingNat B : ℝ) := by
      positivity
    push_cast
    nlinarith

theorem fixedFamilyGeometry_clearing_one (B : ℝ) :
    1 ≤ (fixedFamilyGeometry B).clearing := by
  change (1 : ℝ) ≤ fixedFamilyClearingNat B
  have h : (100 : ℝ) ≤ fixedFamilyClearingNat B := by
    exact_mod_cast fixedFamilyClearingNat_hundred B
  linarith

theorem fixedFamilyGeometry_clearing_threshold (B : ℝ) :
    (fixedCutoffReferenceBandThreshold : ℝ) ≤ (fixedFamilyGeometry B).clearing := by
  change (fixedCutoffReferenceBandThreshold : ℝ) ≤ fixedFamilyClearingNat B
  exact_mod_cast (le_max_right ⌈B⌉₊ fixedCutoffReferenceBandThreshold)

theorem fixedFamilyGeometry_radius_eq (B : ℝ) :
    (fixedFamilyGeometry B).radius =
      (fixedCutoffReferenceRadius : ℝ) * (fixedFamilyGeometry B).clearing := by
  simp [fixedFamilyGeometry]

theorem fixedFamilyGeometry_start_eq_radius (B : ℝ) :
    ((fixedFamilyGeometry B).start : ℝ) = (fixedFamilyGeometry B).radius := rfl

theorem fixedFamilyGeometry_start_ten (B : ℝ) :
    10 ≤ (fixedFamilyGeometry B).start := by
  change 10 ≤ fixedCutoffReferenceRadius * fixedFamilyClearingNat B
  have hC := fixedFamilyClearingNat_hundred B
  have hR := fixedCutoffReferenceRadius_gt_six
  nlinarith

theorem fixedFamilyGeometry_upper_sixteen (B : ℝ) :
    16 ≤ (fixedFamilyGeometry B).upper :=
  (fixedFamilyUpper_bounds B).1

theorem fixedFamilyGeometry_upper_gain (B : ℝ) :
    2 / (π ^ 4 / 625) < (fixedFamilyGeometry B).upper :=
  (fixedFamilyUpper_bounds B).2.1

theorem fixedFamilyGeometry_radius_le_upper_div_sixteen (B : ℝ) :
    (fixedCutoffReferenceRadius : ℝ) * (fixedFamilyGeometry B).clearing ≤
      (fixedFamilyGeometry B).upper / 16 := by
  change (fixedCutoffReferenceRadius : ℝ) * (fixedFamilyClearingNat B : ℝ) ≤
    fixedFamilyUpper B / 16
  have h := (fixedFamilyUpper_bounds B).2.2.1
  linarith

theorem fixedFamilyGeometry_negative_scale (B : ℝ) :
    4 * fixedCutoffReferenceNegativeExponent ^ 2 * (fixedFamilyGeometry B).clearing ≤
      (fixedFamilyGeometry B).upper :=
  (fixedFamilyUpper_bounds B).2.2.2

def fixedFamilyRatio (B : ℝ) : ℝ :=
  (fixedFamilyGeometry B).upper / (fixedFamilyGeometry B).clearing

theorem fixedFamilyGeometry_ratio_one (B : ℝ) : 1 ≤ fixedFamilyRatio B := by
  have hC := fixedFamilyGeometry_clearing_one B
  have hR : (1 : ℝ) ≤ fixedCutoffReferenceRadius := by
    exact_mod_cast (show 1 ≤ fixedCutoffReferenceRadius by
      have := fixedCutoffReferenceRadius_gt_six
      omega)
  have hU := (fixedFamilyGeometry B).radius_le_upper
  rw [fixedFamilyGeometry_radius_eq] at hU
  unfold fixedFamilyRatio
  apply (le_div_iff₀ (by linarith)).mpr
  nlinarith

theorem fixedFamilyGeometry_upper_eq_ratio (B : ℝ) :
    (fixedFamilyGeometry B).upper = fixedFamilyRatio B * (fixedFamilyGeometry B).clearing := by
  have hC := fixedFamilyGeometry_clearing_one B
  unfold fixedFamilyRatio
  rw [div_mul_cancel₀ _ (by linarith)]

end BTZEntropy.Construction
