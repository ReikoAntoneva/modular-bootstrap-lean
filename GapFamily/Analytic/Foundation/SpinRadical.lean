import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Radical estimate on the physical spin cone

The two chiral energies have square roots whose sum is between `sqrt (2 * e)`
and `2 * sqrt e`. These estimates give the explicit exponential constants in
the denominator-one vacuum estimate, including at either boundary `e = |j|`.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped Real

/-- Lower radical-sum bound, valid at the physical cone boundary. -/
theorem sqrt_two_mul_le_sqrt_add_sqrt_sub {e j : ℝ} (h : |j| ≤ e) :
    Real.sqrt (2 * e) ≤ Real.sqrt (e + j) + Real.sqrt (e - j) := by
  obtain ⟨hneg, hpos⟩ := abs_le.mp h
  have hep : 0 ≤ e + j := by linarith
  have hem : 0 ≤ e - j := by linarith
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hep, Real.sq_sqrt hem,
      mul_nonneg (Real.sqrt_nonneg (e + j)) (Real.sqrt_nonneg (e - j))]

/-- Upper radical-sum bound, uniformly in the real spin. -/
theorem sqrt_add_sqrt_sub_le_two_sqrt {e j : ℝ} (h : |j| ≤ e) :
    Real.sqrt (e + j) + Real.sqrt (e - j) ≤ 2 * Real.sqrt e := by
  have he : 0 ≤ e := (abs_nonneg j).trans h
  obtain ⟨hneg, hpos⟩ := abs_le.mp h
  have hep : 0 ≤ e + j := by linarith
  have hem : 0 ≤ e - j := by linarith
  have hp := Real.sqrt_nonneg (e + j)
  have hm := Real.sqrt_nonneg (e - j)
  have hz := Real.sqrt_nonneg e
  nlinarith [Real.sq_sqrt hep, Real.sq_sqrt hem, Real.sq_sqrt he,
    sq_nonneg (Real.sqrt (e + j) - Real.sqrt (e - j))]

/-- The small shift of the vacuum energy preserves a rational fraction of its
square root once the vacuum parameter reaches one hundred. -/
theorem mul_sqrt_le_sqrt_sub_two {a : ℝ} (ha : 100 ≤ a) :
    (49 / 50 : ℝ) * Real.sqrt a ≤ Real.sqrt (a - 2) := by
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 0 ≤ a - 2 := by linarith
  have hs := Real.sqrt_nonneg a
  have ht := Real.sqrt_nonneg (a - 2)
  nlinarith [Real.sq_sqrt ha0, Real.sq_sqrt ha2]

/-- The source's rational lower bound for `sqrt 2`, expressed after scaling. -/
theorem seven_fifths_sqrt_le_sqrt_two_mul {e : ℝ} (he : 0 ≤ e) :
    (7 / 5 : ℝ) * Real.sqrt e ≤ Real.sqrt (2 * e) := by
  have hs := Real.sqrt_nonneg e
  have ht := Real.sqrt_nonneg (2 * e)
  nlinarith [Real.sq_sqrt he, Real.sq_sqrt (show 0 ≤ 2 * e by positivity)]

/-- Explicit lower exponent in the four-seed vacuum estimate, D (40).
The rational comparisons are `π > 31/10`, `sqrt (a-2) ≥ (49/50) sqrt a`,
and `sqrt (2e) ≥ (7/5) sqrt e`. -/
theorem eight_sqrt_mul_le_vacuum_exponent {a e j : ℝ}
    (ha : 100 ≤ a) (he : |j| ≤ e) :
    8 * Real.sqrt (a * e) ≤
      (19 / 20 : ℝ) * π * (Real.sqrt a + Real.sqrt (a - 2)) *
        (Real.sqrt (e + j) + Real.sqrt (e - j)) := by
  have ha0 : 0 ≤ a := by linarith
  have he0 : 0 ≤ e := (abs_nonneg j).trans he
  have hpi : (31 / 10 : ℝ) ≤ π := by linarith [Real.pi_gt_d2]
  have ha' : (99 / 50 : ℝ) * Real.sqrt a ≤
      Real.sqrt a + Real.sqrt (a - 2) := by
    linarith [mul_sqrt_le_sqrt_sub_two ha]
  have he' : (7 / 5 : ℝ) * Real.sqrt e ≤
      Real.sqrt (e + j) + Real.sqrt (e - j) :=
    (seven_fifths_sqrt_le_sqrt_two_mul he0).trans
      (sqrt_two_mul_le_sqrt_add_sqrt_sub he)
  calc
    _ ≤ (19 / 20 : ℝ) * (31 / 10) * ((99 / 50) * Real.sqrt a) *
        ((7 / 5) * Real.sqrt e) := by
      rw [Real.sqrt_mul ha0]
      nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg e)]
    _ ≤ _ := by gcongr

/-- Explicit upper exponent in the four-seed vacuum estimate, D (40). -/
theorem vacuum_exponent_le_four_pi_sqrt {a e j : ℝ}
    (ha : 0 ≤ a) (he : |j| ≤ e) :
    2 * π * Real.sqrt (a * (e + j)) + 2 * π * Real.sqrt (a * (e - j)) ≤
      4 * π * Real.sqrt (a * e) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul ha, Real.sqrt_mul ha]
  calc
    _ = (2 * π * Real.sqrt a) *
        (Real.sqrt (e + j) + Real.sqrt (e - j)) := by ring
    _ ≤ (2 * π * Real.sqrt a) * (2 * Real.sqrt e) := by
      exact mul_le_mul_of_nonneg_left (sqrt_add_sqrt_sub_le_two_sqrt he) (by positivity)
    _ = _ := by ring

end GapFamily.Analytic
