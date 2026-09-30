import GapFamily.Analytic.Kernel.FullKernelInputColumn
import GapFamily.Analytic.Kernel.FullKernelInputStripBound
import GapFamily.Analytic.Kernel.FullKernelInputColumnStripCoefficient

/-!
# Strip growth of the actual input column

The physical Hilbert and ordinary `L¹` columns inherit the same sharp
imaginary-coordinate exponential as the actual pointwise kernel. On a disk
centered on the real axis, the center contributes only to a polynomial.
-/

noncomputable section

open MeasureTheory Real Set Metric
open scoped BigOperators

namespace GapFamily.Analytic

/-- The exact Hilbert moment bound for one row of the actual rectangle column. -/
theorem norm_correctedInputColumnRow_rectangle_le (j jin : ℤ) (B R r : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖correctedInputColumnRow j jin B hB z‖ ≤
      inputColumnStripCoefficient jin B R r * B + 12 * R * sqrt B := by
  apply norm_toLp_le_of_energy_sqrt_bound j B hB _ _
    (inputColumnStripCoefficient jin B R r) (12 * R)
    (inputColumnStripCoefficient_nonneg jin B R r) (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact norm_correctedKernelHolInput_rectangle_le j jin e B R r z he.1.le he.2.le hz him

/-- The exact ordinary mass moment bound for the same rectangle column. -/
theorem norm_correctedInputColumnL1Row_rectangle_le (j jin : ℤ) (B R r : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖correctedInputColumnL1Row j jin B hB z‖ ≤
      inputColumnStripCoefficient jin B R r * B + 12 * R * (B + 2 * sqrt B) := by
  apply norm_toL1_le_of_energy_sqrt_bound j B hB _ _
    (inputColumnStripCoefficient jin B R r) (12 * R)
    (inputColumnStripCoefficient_nonneg jin B R r) (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact norm_correctedKernelHolInput_rectangle_le j jin e B R r z he.1.le he.2.le hz him

private theorem inputColumnStrip_hilbert_norm_le_sum {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, SeminormedAddCommGroup (V i)] (f : PiLp 2 V) :
    ‖f‖ ≤ ∑ i, ‖f i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

/-- The finite Hilbert column retains the rectangle's energy coefficient. -/
theorem norm_correctedInputColumn_rectangle_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (R r : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖correctedInputColumn J B hB jin z‖ ≤ (Fintype.card ι : ℝ) *
      (inputColumnStripCoefficient jin B R r * B + 12 * R * sqrt B) := by
  calc
    _ ≤ ∑ i, ‖correctedInputColumnRow (J i) jin B hB z‖ :=
      inputColumnStrip_hilbert_norm_le_sum _
    _ ≤ ∑ _i : ι, (inputColumnStripCoefficient jin B R r * B + 12 * R * sqrt B) :=
      Finset.sum_le_sum fun i _ =>
        norm_correctedInputColumnRow_rectangle_le (J i) jin B R r hB hR z hz him
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The finite ordinary `L¹` column obeys the corresponding mass estimate. -/
theorem norm_correctedInputColumnL1_rectangle_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (R r : ℝ) (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖correctedInputColumnL1 J B hB jin z‖ ≤ (Fintype.card ι : ℝ) *
      (inputColumnStripCoefficient jin B R r * B + 12 * R * (B + 2 * sqrt B)) := by
  rw [PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _i : ι, (inputColumnStripCoefficient jin B R r * B +
        12 * R * (B + 2 * sqrt B)) :=
      Finset.sum_le_sum fun i _ =>
        norm_correctedInputColumnL1Row_rectangle_le (J i) jin B R r hB hR z hz him
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Only the imaginary width enters the exponential for the physical Hilbert column. -/
theorem norm_correctedInputColumn_strip_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (R r : ℝ)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖correctedInputColumn J B hB jin z‖ ≤
      (Fintype.card ι : ℝ) * inputColumnStripPolynomial jin R * (B + 2 * sqrt B) *
        exp (4 * π * r * sqrt B) := by
  apply (norm_correctedInputColumn_rectangle_le J B hB jin R r hR z hz him).trans
  exact (mul_le_mul_of_nonneg_left
    (inputColumnStripHilbertCoefficient_le jin B R r hB hR hr) (Nat.cast_nonneg _)).trans_eq
    (by ring)

/-- The same imaginary-width exponential controls genuine ordinary mass. -/
theorem norm_correctedInputColumnL1_strip_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (R r : ℝ)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖correctedInputColumnL1 J B hB jin z‖ ≤
      (Fintype.card ι : ℝ) * inputColumnStripPolynomial jin R * (B + 2 * sqrt B) *
        exp (4 * π * r * sqrt B) := by
  apply (norm_correctedInputColumnL1_rectangle_le J B hB jin R r hR z hz him).trans
  exact (mul_le_mul_of_nonneg_left
    (inputColumnStripL1Coefficient_le jin B R r hB hR hr) (Nat.cast_nonneg _)).trans_eq
    (by ring)

private theorem inputColumn_realDisk_bounds (x r : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (x : ℂ) r) : ‖z‖ ≤ |x| + r ∧ |z.im| ≤ r := by
  have hdist : ‖z - (x : ℂ)‖ ≤ r := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  constructor
  · have h := norm_add_le (z - (x : ℂ)) (x : ℂ)
    simp only [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  · have h := (Complex.abs_im_le_norm (z - (x : ℂ))).trans hdist
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using h

/-- A real-center disk changes only the explicit polynomial prefactor. -/
theorem norm_correctedInputColumn_real_disk_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (x r : ℝ)
    (hr : 0 ≤ r) (z : ℂ) (hz : z ∈ closedBall (x : ℂ) r) :
    ‖correctedInputColumn J B hB jin z‖ ≤
      (Fintype.card ι : ℝ) * inputColumnStripPolynomial jin (|x| + r) *
        (B + 2 * sqrt B) * exp (4 * π * r * sqrt B) := by
  obtain ⟨hnorm, him⟩ := inputColumn_realDisk_bounds x r z hz
  exact norm_correctedInputColumn_strip_le J B hB jin (|x| + r) r (by positivity)
    hr z hnorm him

/-- Ordinary mass on a real-center disk has the same polynomial and exponential. -/
theorem norm_correctedInputColumnL1_real_disk_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (x r : ℝ)
    (hr : 0 ≤ r) (z : ℂ) (hz : z ∈ closedBall (x : ℂ) r) :
    ‖correctedInputColumnL1 J B hB jin z‖ ≤
      (Fintype.card ι : ℝ) * inputColumnStripPolynomial jin (|x| + r) *
        (B + 2 * sqrt B) * exp (4 * π * r * sqrt B) := by
  obtain ⟨hnorm, him⟩ := inputColumn_realDisk_bounds x r z hz
  exact norm_correctedInputColumnL1_strip_le J B hB jin (|x| + r) r (by positivity)
    hr z hnorm him

end GapFamily.Analytic
