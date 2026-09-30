import GapFamily.Analytic.Foundation.ReferenceMeasure

/-!
# The quadratic density bound after the physical cell substitution

The input is a lower bound on the actual physical numerator. The denominator
introduced by the reference measure is retained through the calculation.
-/

open Real Set MeasureTheory

namespace GapFamily.Construction

/-- A physical vacuum-type lower bound gives the quadratic lower bound needed
by C3, with its exact reference-measure Jacobian. This includes a spin-opening
endpoint, where the transformed coordinate is zero. -/
theorem coordinate_density_quadratic_lower_bound
    {r L x c P H : ℝ} (hr : 0 ≤ r) (hL : 0 < L)
    (hLx : L ≤ r + x^2) (hc : 0 ≤ c) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (q : ℝ → ℝ)
    (hq : c * ((r+x^2)^2-r^2) * P-H ≤ q (r+x^2)) :
    (2*c*P*sqrt L)*x^2-2*H/sqrt L ≤
      2*q (r+x^2)/sqrt (x^2+2*r) := by
  have hden : L ≤ x^2+2*r := by linarith
  have hs : 0 < sqrt (x^2+2*r) := sqrt_pos.2 (hL.trans_le hden)
  have ht : 0 < sqrt L := sqrt_pos.2 hL
  have hts : sqrt L ≤ sqrt (x^2+2*r) := sqrt_le_sqrt hden
  have hsq := sq_sqrt (show 0 ≤ x^2+2*r by positivity)
  have hraw := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hq (show (0:ℝ) ≤ 2 by norm_num)) hs.le
  have halg : 2*(c*((r+x^2)^2-r^2)*P-H)/sqrt (x^2+2*r) =
      (2*c*P)*x^2*sqrt (x^2+2*r)-2*H/sqrt (x^2+2*r) := by
    apply (div_eq_iff (ne_of_gt hs)).2
    field_simp
    rw [hsq]
    ring
  rw [halg] at hraw
  have hmain := mul_le_mul_of_nonneg_left hts
    (show 0 ≤ (2*c*P)*x^2 by positivity)
  have herr := div_le_div_of_nonneg_left (show 0 ≤ 2*H by positivity) ht hts
  nlinarith

end GapFamily.Construction
