import GapFamily.Analytic.Foundation.Vacuum
import GapFamily.Analytic.Kernel.KernelAnalytic

/-!
# An explicit thermal envelope for the physical tail

The envelope is the actual denominator-one vacuum numerator plus the allowed
tail error. Its uniform exponential bound is independent of the physical spin.
-/

noncomputable section

open Real MeasureTheory
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The concrete reference numerator dominating every allowed tail density. -/
def tailEnvelopeNumerator (a E : ℝ) (j : ℤ) : ℝ :=
  vacuumLeading a E j + exp (7 * sqrt (a * E))

theorem continuous_tailEnvelopeNumerator (a : ℝ) (j : ℤ) :
    Continuous (fun E : ℝ => tailEnvelopeNumerator a E j) := by
  have hc (J : ℤ) (A : ℂ) : Continuous (fun E : ℝ => higherKernelTerm j J E A 0) := by
    have hp : Continuous (fun E : ℝ => ((E : ℂ), A)) :=
      Complex.continuous_ofReal.prodMk continuous_const
    simpa only [Function.comp_def] using (continuous_higherKernelTerm j J 0).comp hp
  have hv : Continuous (fun E : ℝ => vacuumHigherTerm a E j 0) := by
    unfold vacuumHigherTerm
    exact continuous_const.mul
      ((((hc 0 (-a)).sub (hc 1 (1 - a))).sub (hc (-1) (1 - a))).add (hc 0 (2 - a)))
  change Continuous (fun E : ℝ => (vacuumHigherTerm a E j 0).re + exp (7 * sqrt (a * E)))
  exact (Complex.continuous_re.comp hv).add
    (continuous_exp.comp (continuous_const.mul (continuous_const.mul continuous_id).sqrt))

theorem measurable_tailEnvelopeNumerator (a : ℝ) (j : ℤ) :
    Measurable (fun E : ℝ => tailEnvelopeNumerator a E j) :=
  (continuous_tailEnvelopeNumerator a j).measurable

theorem tailEnvelopeNumerator_nonneg (a E : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (hj : |(j : ℝ)| ≤ E) :
    0 ≤ tailEnvelopeNumerator a E j :=
  add_nonneg (vacuumLeading_nonneg a E j ha hj) (exp_pos _).le

/-- The vacuum and error share one square-root exponential growth envelope. -/
theorem tailEnvelopeNumerator_le_exp (a E : ℝ) (j : ℤ)
    (ha : 100 ≤ a) (hj : |(j : ℝ)| ≤ E) :
    tailEnvelopeNumerator a E j ≤ 3 * exp ((4 * π * sqrt a) * sqrt E) := by
  have hmain := vacuumLeading_le_exp a E j (by linarith) hj
  have herror : exp (7 * sqrt (a * E)) ≤ exp (4 * π * sqrt (a * E)) := by
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith [pi_gt_three] : (7 : ℝ) ≤ 4 * π)
      (sqrt_nonneg _)
  have hroot : sqrt (a * E) = sqrt a * sqrt E := sqrt_mul (by linarith : 0 ≤ a) E
  dsimp [tailEnvelopeNumerator]
  simp only [hroot, mul_assoc] at hmain herror ⊢
  linarith

/-- A positive-energy thermal tilt is dominated by the ordinary
energy-weighted square-root exponential profile used for summing spins. -/
theorem thermal_tailEnvelopeNumerator_le (a E t : ℝ) (j : ℤ)
    (ha : 100 ≤ a) (hE : 1 ≤ E) (hj : |(j : ℝ)| ≤ E) :
    exp (-t * E) * tailEnvelopeNumerator a E j ≤
      3 * (E * exp ((4 * π * sqrt a) * sqrt E - t * E)) := by
  calc
    _ ≤ exp (-t * E) * (3 * exp ((4 * π * sqrt a) * sqrt E)) :=
      mul_le_mul_of_nonneg_left (tailEnvelopeNumerator_le_exp a E j ha hj) (exp_pos _).le
    _ = 3 * exp ((4 * π * sqrt a) * sqrt E - t * E) := by
      rw [sub_eq_add_neg, exp_add]
      simp only [neg_mul]
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hE
        (exp_pos ((4 * π * sqrt a) * sqrt E - t * E)).le
      nlinarith

end GapFamily.Construction
