import GapFamily.Construction.CellCoordinateVacuum
import GapFamily.Analytic.Kernel.FullKernelSmoothingMoment

/-! Pointwise lower and ordinary mass bounds for a reference numerator whose
proved error is absorbed by the actual denominator-one vacuum. -/

noncomputable section

open Real Set MeasureTheory
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A full unit past the spin edge supplies a uniform positive quadratic factor. -/
theorem one_le_energy_sq_sub_spin_sq (j : ℤ) {e : ℝ}
    (he : |(j : ℝ)| + 1 ≤ e) : 1 ≤ e ^ 2 - (j : ℝ) ^ 2 := by
  have h := abs_nonneg (j : ℝ)
  have hs : |(j : ℝ)| ^ 2 = (j : ℝ) ^ 2 := sq_abs _
  nlinarith

/-- Beyond the first unit of a physical row, the vacuum lower bound absorbs
the complete allowed error and retains half its leading lower estimate. -/
theorem referenceDensity_lower_of_vacuum_error
    (j : ℤ) {a e : ℝ} (ha : 100 ≤ a) (he : |(j : ℝ)| + 1 ≤ e)
    (q : ℝ → ℝ) (herr : |q e - vacuumLeading a e j| ≤ exp (7 * sqrt (a * e))) :
    (π ^ 4 / 625) * (e ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * e)) ≤ q e := by
  have he1 : 1 ≤ e := by linarith [abs_nonneg (j : ℝ)]
  have hj : |(j : ℝ)| ≤ e := by linarith
  have hedge := one_le_energy_sq_sub_spin_sq j he
  have hx : 10 ≤ sqrt (a * e) := by
    apply (le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith
  have hp : (81 : ℝ) ≤ π ^ 4 := by
    have hpi := Real.pi_gt_three
    nlinarith [sq_nonneg (π ^ 2 - 9)]
  have hc : 1 ≤ (π ^ 4 / 625) * (e ^ 2 - (j : ℝ) ^ 2) * exp (sqrt (a * e)) := by
    have hexp : 11 ≤ exp (sqrt (a * e)) := by
      linarith [Real.add_one_le_exp (sqrt (a * e))]
    calc
      _ ≤ (81 / 625 : ℝ) * 1 * 11 := by norm_num
      _ ≤ _ := by gcongr
  have habsorb : exp (7 * sqrt (a * e)) ≤
      (π ^ 4 / 625) * (e ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * e)) := by
    calc
      _ ≤ ((π ^ 4 / 625) * (e ^ 2 - (j : ℝ) ^ 2) * exp (sqrt (a * e))) *
          exp (7 * sqrt (a * e)) := le_mul_of_one_le_left (exp_nonneg _) hc
      _ = _ := by rw [mul_assoc, ← exp_add]; congr 2; ring
  have hleading := vacuumLeading_ge_exp a e j ha hj
  have herror := (abs_le.mp herr).1
  nlinarith

/-- The actual reference is strictly positive after the first unit of each
row whenever its proved vacuum approximation bound applies. -/
theorem referenceDensity_pos_of_vacuum_error
    (j : ℤ) {a e : ℝ} (ha : 100 ≤ a) (he : |(j : ℝ)| + 1 ≤ e)
    (q : ℝ → ℝ) (herr : |q e - vacuumLeading a e j| ≤ exp (7 * sqrt (a * e))) :
    0 < q e := by
  have hedge := one_le_energy_sq_sub_spin_sq j he
  exact lt_of_lt_of_le (by positivity) (referenceDensity_lower_of_vacuum_error j ha he q herr)

/-- The same approximation gives a simple absolute upper bound with the
original vacuum exponent, uniformly over all physical spins. -/
theorem abs_referenceDensity_le_of_vacuum_error
    (j : ℤ) {a e : ℝ} (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e)
    (q : ℝ → ℝ) (herr : |q e - vacuumLeading a e j| ≤ exp (7 * sqrt (a * e))) :
    |q e| ≤ 3 * exp (4 * π * sqrt (a * e)) := by
  have hv := vacuumLeading_nonneg a e j ha he
  have hlead := vacuumLeading_le_exp a e j ha he
  have hexp : exp (7 * sqrt (a * e)) ≤ exp (4 * π * sqrt (a * e)) := by
    apply exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
    linarith [Real.pi_gt_three]
  calc
    |q e| = |(q e - vacuumLeading a e j) + vacuumLeading a e j| := by ring_nf
    _ ≤ |q e - vacuumLeading a e j| + |vacuumLeading a e j| := abs_add_le _ _
    _ ≤ exp (7 * sqrt (a * e)) + 2 * exp (4 * π * sqrt (a * e)) := by
      rw [abs_of_nonneg hv]
      exact add_le_add herr hlead
    _ ≤ _ := by linarith

end GapFamily.Construction
