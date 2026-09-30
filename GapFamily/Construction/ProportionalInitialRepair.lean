import GapFamily.Construction.ProportionalInitialGeometry
import GapFamily.Construction.RealInitialCellMass
import GapFamily.Construction.InitialReferenceRepairBudgetCell
import GapFamily.Construction.InitialReferenceRepairBudgetRow

/-!
# Actual initial exterior repair at real proportional parameters

The frozen Cauchy ratio depends only on `s`. The compact-mass coefficient
may depend on the cutoff-to-marker ratio `Q`, while its exponential rate is
uniform in `Q`. This separates the ordered auxiliary choice from the later
real gap ratio.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

/-- A coefficient for one real-parameter initial cell. -/
def proportionalInitialRepairCellBudget (Q a : ℝ) (s : ℕ) (B : ℝ) : ℝ :=
  2 * canonicalRepairCellCoefficient * markerReferenceCompactMassCoefficient (Q + 1) *
    (1 + a + B) ^ 10 *
    exp (2 * markerReferenceCompactMassExponent 2 * (proportionalDegree a s : ℝ) +
      canonicalRepairKernelExponent * B) / (initialRepairRatio s) ^ proportionalDegree a s

/-- The finite row factor is included in this normalized total budget. -/
def proportionalInitialRepairBudget (Q a : ℝ) (s : ℕ) (B : ℝ) : ℝ :=
  20 * canonicalRepairCellCoefficient * markerReferenceCompactMassCoefficient (Q + 1) *
    (1 + a + B) ^ 11 *
    exp (2 * markerReferenceCompactMassExponent 2 * (proportionalDegree a s : ℝ) +
      canonicalRepairKernelExponent * B) / (initialRepairRatio s) ^ proportionalDegree a s

/-- The literal real exterior numerator obeys the budget for the floor
degree. In particular no integral relation between the gap and charge is
used by the actual analytic repair. -/
theorem InitialReferenceCell.abs_exteriorNumerator_le_proportional_budget
    {a b Q : ℝ} {s : ℕ} {jin : ℤ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cell : InitialReferenceCell jin (max b |(jin : ℝ)|) (proportionalCutoff a s)
      (proportionalDegree a s) (canonicalMarkerReferenceDensity a b ha hb jin))
    (hs : 1 ≤ s) (hρ : 2 ≤ initialRepairRatio s)
    (hU : 1 ≤ proportionalCutoff a s) (hlarge : 2 ≤ a / s)
    (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : proportionalCutoff a s = Q * b)
    (B : ℝ) (hB : 1 ≤ B) (hcut : cell.right < B)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    |cell.exteriorNumerator B hB j e| ≤
      proportionalInitialRepairCellBudget Q a s B * exp (7 * sqrt (a * e)) := by
  have hwidth : sqrtInputWidth jin (max b |(jin : ℝ)|) cell.right / (sqrt a / 100) ≤
      1 / initialRepairRatio s := by
    simpa only [sqrtInputWidth, cellCoordinateLength, rootCoord] using
      proportional_initial_cell_cauchy_ratio_le (by linarith : 0 < a) hs
        (abs_nonneg (jin : ℝ)) hU cell.right_mem.2
  have hbase := norm_initialRepairKernel_le_normalized B hB j jin e a (initialRepairRatio s)
    he hBe (by linarith) hρ cell.residual (max b |(jin : ℝ)|) cell.right
    (proportionalDegree a s) (le_max_right _ _) cell.left_le_right hcut.le hwidth
    cell.ae_mem_cell (fun m hm => cell.signedSqrtCoordinate_moment_zero m hm)
  rw [SignedMeasure.totalVariation_eq_variation] at hbase
  have hroot : sqrt (a * proportionalCutoff a s) ≤ 2 * (proportionalDegree a s : ℝ) := by
    rw [proportionalParameter_sqrt_aU (by linarith)]
    have hh := proportionalParameter_half_le_degree hlarge
    have heq : a / (2 * s) = (a / s) / 2 := by ring
    rw [heq] at hh
    linarith
  have hC := canonicalRepairCellCoefficient_pos.le
  have hM := (markerReferenceCompactMassCoefficient_pos (Q + 1) (by linarith)).le
  have hE := (markerReferenceCompactMassExponent_pos 2).le
  have hρ0 : 0 < initialRepairRatio s := by linarith
  have htv : cell.residual.variation.real univ ≤
      2 * markerReferenceCompactMassCoefficient (Q + 1) * (1 + a + B) ^ 9 *
        exp (2 * markerReferenceCompactMassExponent 2 * (proportionalDegree a s : ℝ)) := by
    refine (cell.variation_le_canonical_endpoint Q hQ hba hQU).trans ?_
    have hpoly : (1 + a) ^ 9 ≤ (1 + a + B) ^ 9 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 9
    have hexp : exp (markerReferenceCompactMassExponent 2 *
        sqrt (a * proportionalCutoff a s)) ≤
        exp (2 * markerReferenceCompactMassExponent 2 * (proportionalDegree a s : ℝ)) :=
      exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by positivity)) hexp
      (exp_nonneg _) (by positivity)
  have hcanonical : ‖canonicalRepairExteriorNumerator (singleSpinInput jin cell.residual)
      B hB j e‖ ≤ proportionalInitialRepairCellBudget Q a s B * exp (7 * sqrt (a * e)) := by
    rw [canonicalRepairExteriorNumerator_singleSpin jin cell.residual B hB
      (singleSpinInput_mem_lowBandSpinSet jin B (max b |(jin : ℝ)|) cell.right
        (le_max_right _ _) cell.left_le_right hcut)]
    refine hbase.trans ?_
    calc
      _ ≤ canonicalRepairCellCoefficient *
          (2 * markerReferenceCompactMassCoefficient (Q + 1) * (1 + a + B) ^ 9 *
            exp (2 * markerReferenceCompactMassExponent 2 * (proportionalDegree a s : ℝ))) *
          (1 + a + B) * exp (canonicalRepairKernelExponent * B) /
            (initialRepairRatio s) ^ proportionalDegree a s * exp (7 * sqrt (a * e)) := by
        gcongr
      _ = _ := by unfold proportionalInitialRepairCellBudget; rw [exp_add]; ring
  exact (Complex.abs_re_le_norm _).trans hcanonical

/-- Any finite family covering the initial rows has the actual normalized
repair estimate as soon as its cardinality has the elementary linear bound. -/
theorem sum_abs_proportionalInitialRepairExterior_le_budget
    {S : Finset ℤ} {a b Q : ℝ} {s : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cells : ∀ J : S, InitialReferenceCell J (max b |(J : ℝ)|) (proportionalCutoff a s)
      (proportionalDegree a s) (canonicalMarkerReferenceDensity a b ha hb J))
    (hs : 1 ≤ s) (hρ : 2 ≤ initialRepairRatio s)
    (hU : 1 ≤ proportionalCutoff a s) (hlarge : 2 ≤ a / s)
    (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : proportionalCutoff a s = Q * b)
    (hcard : (S.card : ℝ) ≤ 10 * (1 + a))
    (B : ℝ) (hB : 1 ≤ B) (hcut : ∀ J, (cells J).right < B)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    (∑ J, |(cells J).exteriorNumerator B hB j e|) ≤
      proportionalInitialRepairBudget Q a s B * exp (7 * sqrt (a * e)) := by
  let X : ℝ := 1 + a + B
  let C : ℝ := 2 * canonicalRepairCellCoefficient * markerReferenceCompactMassCoefficient (Q + 1) *
    exp (2 * markerReferenceCompactMassExponent 2 * (proportionalDegree a s : ℝ) +
      canonicalRepairKernelExponent * B) / (initialRepairRatio s) ^ proportionalDegree a s *
    exp (7 * sqrt (a * e))
  have hC : 0 ≤ C := by
    have := canonicalRepairCellCoefficient_pos
    have := markerReferenceCompactMassCoefficient_pos (Q + 1) (by linarith)
    have hρ0 : 0 < initialRepairRatio s := by linarith
    dsimp [C]
    positivity
  have hcard' : (Fintype.card S : ℝ) ≤ 10 * X := by
    simpa only [Fintype.card_coe] using hcard.trans (show 10 * (1 + a) ≤ 10 * X by
      dsimp [X]; linarith)
  have hsum := initialReference_fintype_sum_prefactor 10 hC (show 0 ≤ X by dsimp [X]; linarith)
    hcard' (fun J : S => |(cells J).exteriorNumerator B hB j e|) (fun J => by
      have hcell := (cells J).abs_exteriorNumerator_le_proportional_budget
        hs hρ hU hlarge hQ hba hQU B hB (hcut J) j e he hBe
      convert hcell using 1
      dsimp [C, X, proportionalInitialRepairCellBudget]
      ring)
  convert hsum using 1
  dsimp [C, X, proportionalInitialRepairBudget]
  ring

end GapFamily.Construction
