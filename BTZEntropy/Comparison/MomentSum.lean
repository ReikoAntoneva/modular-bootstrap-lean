import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Aggregating local comparison errors

A cell error bounded by its mass times a common accuracy can be summed with
nonnegative weights. The infinite version derives summability from the weighted
mass majorant, so the estimate applies to actual convergent sums.
-/

namespace BTZEntropy.Comparison

variable {ι : Type*}

/-- Multiply a local absolute error bound by a nonnegative weight. -/
theorem abs_weighted_error_le {w m e ε : ℝ} (hw : 0 ≤ w)
    (he : |e| ≤ m * ε) : |w * e| ≤ (w * m) * ε := by
  rw [abs_mul, abs_of_nonneg hw, mul_assoc]
  exact mul_le_mul_of_nonneg_left he hw

/-- Finite weighted cell errors are controlled by total weighted mass. -/
theorem abs_weighted_sum_le (s : Finset ι) (w m e : ι → ℝ) (ε : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (he : ∀ i ∈ s, |e i| ≤ m i * ε) :
    |∑ i ∈ s, w i * e i| ≤ (∑ i ∈ s, w i * m i) * ε := by
  calc
    |∑ i ∈ s, w i * e i| ≤ ∑ i ∈ s, |w i * e i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (w i * m i) * ε :=
      Finset.sum_le_sum fun i hi => abs_weighted_error_le (hw i hi) (he i hi)
    _ = (∑ i ∈ s, w i * m i) * ε := by rw [Finset.sum_mul]

/-- A summable weighted mass majorant makes the weighted cell errors summable. -/
theorem summable_weighted_error (w m e : ι → ℝ) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (he : ∀ i, |e i| ≤ m i * ε)
    (hm : Summable fun i => w i * m i) : Summable fun i => w i * e i := by
  apply (hm.mul_right ε).of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs] using abs_weighted_error_le (hw i) (he i)

/-- The absolute weighted cell errors are also summable. -/
theorem summable_abs_weighted_error (w m e : ι → ℝ) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (he : ∀ i, |e i| ≤ m i * ε)
    (hm : Summable fun i => w i * m i) : Summable fun i => |w i * e i| := by
  apply (hm.mul_right ε).of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs, abs_abs] using abs_weighted_error_le (hw i) (he i)

/-- The full weighted error is bounded by accuracy times total weighted mass. -/
theorem abs_weighted_tsum_le (w m e : ι → ℝ) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (he : ∀ i, |e i| ≤ m i * ε)
    (hm : Summable fun i => w i * m i) :
    |∑' i, w i * e i| ≤ (∑' i, w i * m i) * ε := by
  have h := tsum_of_norm_bounded (hm.mul_right ε).hasSum
    (fun i => show ‖w i * e i‖ ≤ (w i * m i) * ε by
      simpa only [Real.norm_eq_abs] using abs_weighted_error_le (hw i) (he i))
  simpa only [Real.norm_eq_abs, tsum_mul_right] using h

/-- Compare two finite weighted observables using their local cell differences. -/
theorem abs_weighted_sum_sub_le (s : Finset ι) (w m f g : ι → ℝ) (ε : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (he : ∀ i ∈ s, |f i - g i| ≤ m i * ε) :
    |(∑ i ∈ s, w i * f i) - ∑ i ∈ s, w i * g i| ≤
      (∑ i ∈ s, w i * m i) * ε := by
  simpa only [mul_sub, Finset.sum_sub_distrib] using
    abs_weighted_sum_le s w m (fun i => f i - g i) ε hw he

/-- Compare two convergent weighted observables using their local differences. -/
theorem abs_weighted_tsum_sub_le (w m f g : ι → ℝ) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (he : ∀ i, |f i - g i| ≤ m i * ε)
    (hm : Summable fun i => w i * m i)
    (hf : Summable fun i => w i * f i) (hg : Summable fun i => w i * g i) :
    |(∑' i, w i * f i) - ∑' i, w i * g i| ≤
      (∑' i, w i * m i) * ε := by
  simpa only [mul_sub, hf.tsum_sub hg] using
    abs_weighted_tsum_le w m (fun i => f i - g i) ε hw he hm

end BTZEntropy.Comparison
