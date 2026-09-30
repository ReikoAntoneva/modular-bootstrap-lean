import GapFamily.Construction.CellReserve
import GapFamily.Analytic.Foundation.FullVacuumReality

/-! Upper mass estimates for an actual tail numerator close to the
canonical denominator-one vacuum. The charge threshold remains uniform over
all physical spins and all unbounded tail energies. -/

noncomputable section
open Set MeasureTheory Real Filter
open GapFamily.Analytic
open scoped Topology

namespace GapFamily.Construction

/-- The leading vacuum and the allowed C8 error give one elementary
exponential bound on the whole physical tail cell. -/
theorem tailCell_abs_numerator_le {a L : ℝ} (ha : 100 ≤ a) (hL : 1 ≤ L)
    (j : ℤ) (hj : |(j : ℝ)| ≤ L) (q : ℝ → ℝ)
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    ∀ E ∈ Icc L (L + 1), |q E| ≤ 3 * exp (4 * π * (a + L)) := by
  intro E hE
  have ha0 : 0 ≤ a := by linarith
  have hE0 : 0 ≤ E := by linarith [hE.1]
  have hjE : |(j : ℝ)| ≤ E := hj.trans hE.1
  have hroot : sqrt (a * E) ≤ a + L := by
    apply (sqrt_le_iff).mpr
    refine ⟨by linarith, ?_⟩
    have hmul := mul_le_mul_of_nonneg_left hE.2 ha0
    have hAA := mul_nonneg ha0 (show 0 ≤ a - 1 by linarith)
    have hAL := mul_nonneg ha0 (show 0 ≤ L by linarith)
    nlinarith [sq_nonneg L]
  have hpi : 7 ≤ 4 * π := by linarith [Real.pi_gt_three]
  have hlow := vacuumLeading_nonneg a E j (by linarith) hjE
  have hmain := vacuumLeading_le_exp a E j (by linarith) hjE
  have hmainExp : exp (4 * π * sqrt (a * E)) ≤ exp (4 * π * (a + L)) := by
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hroot (by positivity)
  have herrorExp : exp (7 * sqrt (a * E)) ≤ exp (4 * π * (a + L)) := by
    apply exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right hpi (sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hroot (by positivity))
  calc
    |q E| = |(q E - vacuumLeading a E j) + vacuumLeading a E j| := by congr 1; ring
    _ ≤ |q E - vacuumLeading a E j| + |vacuumLeading a E j| := abs_add_le _ _
    _ ≤ exp (7 * sqrt (a * E)) + 2 * exp (4 * π * sqrt (a * E)) := by
      rw [abs_of_nonneg hlow]
      exact add_le_add (herror E hE) hmain
    _ ≤ 3 * exp (4 * π * (a + L)) := by linarith

/-- The logarithmic repair cost is linear in charge plus the actual left
endpoint, once ordinary total variation has its tail-cell mass bound. -/
theorem tailCell_log_variation_le {a L v : ℝ} (ha : 1 ≤ a) (hL : 1 ≤ L)
    (hv : 0 ≤ v) (hbound : v ≤ 12 * exp (4 * π * (a + L))) :
    log (2 + v) ≤ (4 * π + 14) * (a + L) := by
  have hs : 1 ≤ a + L := by linarith
  have hexp : 1 ≤ exp (4 * π * (a + L)) := one_le_exp (by positivity)
  have hb : 2 + v ≤ 14 * exp (4 * π * (a + L)) := by linarith
  have hlog := log_le_log (show 0 < 2 + v by linarith) hb
  rw [log_mul (by norm_num : (14 : ℝ) ≠ 0) (exp_pos _).ne', log_exp] at hlog
  have h14 : log (14 : ℝ) ≤ 13 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 14)
    norm_num at h
    exact h
  nlinarith

/-- A perturbation using at most three quarters of the error allowance
preserves C8 for the actual full four-seed vacuum numerator. -/
theorem exists_vacuumPerturbation_tail_error_threshold :
    ∃ A : ℝ, 100 ≤ A ∧ ∀ (a L : ℝ) (j : ℤ),
      A ≤ a → 1 ≤ L → |(j : ℝ)| ≤ L → ∀ q : ℝ → ℝ,
      (∀ E ∈ Icc L (L + 1),
        |q E - vacuumNumerator a E j| ≤ (3 / 4 : ℝ) * exp (7 * sqrt (a * E))) →
      ∀ E ∈ Icc L (L + 1),
        |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E)) := by
  obtain ⟨A, hA, hb⟩ := exists_vacuumNumerator_uniform_error_bound
  refine ⟨A, hA, ?_⟩
  intro a L j ha hL hj q hq E hE
  have hh := hb a E j ha (hL.trans hE.1) (hj.trans hE.1)
  calc
    |q E - vacuumLeading a E j| =
        |(q E - vacuumNumerator a E j) + (vacuumNumerator a E j - vacuumLeading a E j)| := by
      congr 1
      ring
    _ ≤ |q E - vacuumNumerator a E j| + |vacuumNumerator a E j - vacuumLeading a E j| :=
      abs_add_le _ _
    _ ≤ exp (7 * sqrt (a * E)) := by linarith [hq E hE]

end GapFamily.Construction
