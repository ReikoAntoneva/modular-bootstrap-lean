import GapFamily.Construction.CellCoordinate
import GapFamily.Analytic.Foundation.Vacuum

/-! The actual denominator-one vacuum bound transported to a physical cell coordinate. -/

noncomputable section

open Set Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A uniform vacuum approximation error gives an explicit numerator lower bound on a cell. -/
theorem cell_numerator_lower_bound_of_vacuum_error
    (j : ℤ) {a L W : ℝ} (ha : 100 ≤ a) (hL : |(j : ℝ)| ≤ L)
    (q : ℝ → ℝ)
    (herror : ∀ E ∈ Icc L W,
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    ∀ E ∈ Icc L W,
      (2 * π ^ 4 / 625) * (E ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * L)) -
        exp (7 * sqrt (a * W)) ≤ q E := by
  intro E hE
  have ha0 : 0 ≤ a := by linarith
  have hjE : |(j : ℝ)| ≤ E := hL.trans hE.1
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hjE
  have hedge : 0 ≤ E ^ 2 - (j : ℝ) ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg (j : ℝ)) hE0).mpr hjE
    simpa only [sq_abs] using sub_nonneg.mpr hsq
  have hlowexp : exp (8 * sqrt (a * L)) ≤ exp (8 * sqrt (a * E)) := by
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE.1 ha0))
      (by norm_num)
  have hupexp : exp (7 * sqrt (a * E)) ≤ exp (7 * sqrt (a * W)) := by
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE.2 ha0))
      (by norm_num)
  have hleading :
      (2 * π ^ 4 / 625) * (E ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * L)) ≤
        vacuumLeading a E j :=
    (mul_le_mul_of_nonneg_left hlowexp (mul_nonneg (by positivity) hedge)).trans
      (vacuumLeading_ge_exp a E j ha hjE)
  have herr := (abs_le.mp (herror E hE)).1
  linarith

/-- The vacuum edge factor supplies the quadratic lower bound in the actual cell coordinate. -/
theorem cellCoordinateDensity_lower_bound_of_vacuum_error
    (j : ℤ) {a L W : ℝ} (ha : 100 ≤ a) (hLpos : 0 < L)
    (hL : |(j : ℝ)| ≤ L) (hLW : L ≤ W)
    (q : ℝ → ℝ)
    (herror : ∀ E ∈ Icc L W,
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    ∀ x ∈ Icc (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| W),
      (2 * (2 * π ^ 4 / 625) * exp (8 * sqrt (a * L)) * sqrt L) * x ^ 2 -
        2 * exp (7 * sqrt (a * W)) / sqrt L ≤ cellCoordinateDensity j q x :=
  cellCoordinateDensity_lower_bound_of_numerator j hLpos hL hLW
    (by positivity) (exp_nonneg _) (exp_nonneg _) q
    (cell_numerator_lower_bound_of_vacuum_error j ha hL q herror)

end GapFamily.Construction
