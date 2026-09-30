import GapFamily.Construction.InitialReferenceCellMass

/-!
# Initial-cell mass with a uniform exponential rate

The compact-mass prefactor may depend on the ratio between the processing
cutoff and the marker. Its exponential rate is bounded by one fixed
constant times `sqrt (a U)`, even when that ratio is arbitrarily large.
This is needed to fix the repair approximation ratio before the real gap
ratio is selected.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The exponential compact-mass rate is uniform in the band ratio when
expressed in the initial endpoint scale. -/
theorem markerReferenceCompactMassExponent_mul_sqrt_le
    {a b U R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 1 ≤ R) (hU : U = R * b) :
    markerReferenceCompactMassExponent (R + 1) * sqrt (a * b) ≤
      markerReferenceCompactMassExponent 2 * sqrt (a * U) := by
  have hbU : b ≤ U := by rw [hU]; exact le_mul_of_one_le_left hb hR
  have hroot : sqrt (a * b) ≤ sqrt (a * U) := sqrt_le_sqrt (by gcongr)
  have hmix : sqrt (R + 1) * sqrt (a * b) ≤ sqrt 2 * sqrt (a * U) := by
    rw [← sqrt_mul (show 0 ≤ R + 1 by linarith), ← sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    apply sqrt_le_sqrt
    calc
      (R + 1) * (a * b) = a * (U + b) := by rw [hU]; ring
      _ ≤ 2 * (a * U) := by nlinarith [mul_le_mul_of_nonneg_left hbU ha]
  have hC : 0 ≤ 4 * π + markerReferenceInputExponent := by
    have := markerReferenceInputExponent_pos
    positivity
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hroot hC)
    (mul_le_mul_of_nonneg_left hmix (show 0 ≤ 4 * π by positivity))
  unfold markerReferenceCompactMassExponent
  nlinarith [hsum]

/-- The actual residual variation has a fixed endpoint exponential rate;
only its polynomial coefficient depends on the cutoff-to-marker ratio. -/
theorem InitialReferenceCell.variation_le_canonical_endpoint
    {a b U : ℝ} {j : ℤ} {k : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cell : InitialReferenceCell j (max b |(j : ℝ)|) U k
      (canonicalMarkerReferenceDensity a b ha hb j))
    (R : ℝ) (hR : 1 ≤ R) (hba : b ≤ a) (hU : U = R * b) :
    cell.residual.variation.real univ ≤
      2 * markerReferenceCompactMassCoefficient (R + 1) * (1 + a) ^ 9 *
        exp (markerReferenceCompactMassExponent 2 * sqrt (a * U)) := by
  refine (cell.variation_le_canonical R hR hba hU).trans ?_
  have hC := markerReferenceCompactMassCoefficient_pos (R + 1) (by linarith)
  have hexp := exp_le_exp.mpr (markerReferenceCompactMassExponent_mul_sqrt_le
    (by linarith : 0 ≤ a) (by linarith : 0 ≤ b) hR hU)
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

end GapFamily.Construction
