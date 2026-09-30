import GapFamily.Analytic.Foundation.ReferenceMeasure

/-!
# Terminal lower bound for the weighted initial reference density

The physical reference weight cancels one square root of the quadratic
edge factor. Beyond the terminal energy, the remaining factor is uniformly
bounded below.
-/

noncomputable section

open Real
open GapFamily.Analytic

namespace GapFamily.Construction

theorem initialReference_terminal_sqrt_lower {U E : ℝ} (j : ℤ)
    (hU : 1 ≤ U) (hj : |(j : ℝ)| ≤ U / 16) (hE : U ≤ E) :
    U / 2 ≤ sqrt (E ^ 2 - (j : ℝ) ^ 2) := by
  have hU0 : 0 ≤ U := by linarith
  have hE0 : 0 ≤ E := hU0.trans hE
  have hjhalf : |(j : ℝ)| ≤ U / 2 := by linarith
  have hjsq : (j : ℝ) ^ 2 ≤ (U / 2) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (j : ℝ)) (by positivity : 0 ≤ U / 2)).mpr hjhalf
  have hEsq : U ^ 2 ≤ E ^ 2 := (sq_le_sq₀ hU0 hE0).mpr hE
  have hsquare : (U / 2) ^ 2 ≤ E ^ 2 - (j : ℝ) ^ 2 := by
    nlinarith [sq_nonneg U]
  simpa only [sqrt_sq (by positivity : 0 ≤ U / 2)] using sqrt_le_sqrt hsquare

/-- A pointwise reference lower bound gives uniform positive physical mass density. -/
theorem initialReference_terminal_weighted_density_lower {c a U E qE : ℝ} (j : ℤ)
    (hc : 0 ≤ c) (_ha : 0 ≤ a) (hU : 1 ≤ U)
    (hj : |(j : ℝ)| ≤ U / 16) (hE : U ≤ E)
    (hq : c * (E ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * E)) ≤ qE) :
    c * U / 2 ≤ referenceDensity j E * qE := by
  have hsqrt := initialReference_terminal_sqrt_lower j hU hj hE
  have hroot : 0 < sqrt (E ^ 2 - (j : ℝ) ^ 2) := by linarith
  have hgap : 0 ≤ E ^ 2 - (j : ℝ) ^ 2 := (sqrt_pos.mp hroot).le
  have hexp : 1 ≤ exp (8 * sqrt (a * E)) := one_le_exp_iff.mpr (by positivity)
  have hqbase : c * (E ^ 2 - (j : ℝ) ^ 2) ≤ qE := by
    exact (le_mul_of_one_le_right (mul_nonneg hc hgap) hexp).trans hq
  calc
    c * U / 2 = c * (U / 2) := by ring
    _ ≤ c * sqrt (E ^ 2 - (j : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hsqrt hc
    _ = referenceDensity j E * (c * (E ^ 2 - (j : ℝ) ^ 2)) := by
      dsimp only [referenceDensity]
      rw [← sq_sqrt hgap]
      field_simp
      simp only [sqrt_sq (sqrt_nonneg _)]
    _ ≤ referenceDensity j E * qE :=
      mul_le_mul_of_nonneg_left hqbase (referenceDensity_nonneg j E)

end GapFamily.Construction
