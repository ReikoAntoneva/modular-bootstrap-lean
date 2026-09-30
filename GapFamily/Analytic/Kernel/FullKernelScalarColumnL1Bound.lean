import GapFamily.Analytic.Kernel.FullKernelScalarColumnBound
import GapFamily.Analytic.Kernel.FullKernelSmoothingOperator

/-!
# Ordinary scalar column mass

The complex scalar column and its disk majorant are integrable against the
actual reference measure. The first and square-root energy moments give a
uniform ordinary mass bound without a finite reference-mass assumption.
-/

noncomputable section

open MeasureTheory Real Set

namespace GapFamily.Analytic

theorem scalarColumnMajorant_integrable (j : ℤ) (B R : ℝ) :
    Integrable (scalarColumnMajorant B R)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  ((lowBand_energy_integrable j B).const_mul
    (higherKernelCompactBound 0 B (B * R ^ 2))).add
    ((lowBand_sqrt_energy_integrable j B).const_mul (12 * sqrt B * R))

/-- The same local majorant can be used for ordinary `L¹`-valued holomorphy. -/
theorem scalarColumnMajorant_memLp_one (j : ℤ) (B : ℝ) (_hB : 0 ≤ B) (R : ℝ) :
    MemLp (scalarColumnMajorant B R) 1
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  memLp_one_iff_integrable.mpr (scalarColumnMajorant_integrable j B R)

/-- The actual complex column is ordinarily integrable, including the scalar row. -/
theorem correctedKernelHolInput_scalar_integrable (j : ℤ) (B : ℝ)
    (hB : 0 ≤ B) (z : ℂ) :
    Integrable (fun e : ℝ => correctedKernelHolInput j 0 B e z)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  apply (scalarColumnMajorant_integrable j B ‖z‖).mono'
    (continuous_correctedKernelHolInput_scalar j B z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact norm_correctedKernelHolInput_scalar_le j B ‖z‖ e z hB (norm_nonneg _)
    he.1.le he.2.le le_rfl

theorem correctedKernelHolInput_scalar_memLp_one (j : ℤ) (B : ℝ)
    (hB : 0 ≤ B) (z : ℂ) :
    MemLp (fun e : ℝ => correctedKernelHolInput j 0 B e z) 1
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  memLp_one_iff_integrable.mpr (correctedKernelHolInput_scalar_integrable j B hB z)

/-- Disk-uniform bound for the actual ordinary mass of the scalar column. -/
theorem integral_norm_correctedKernelHolInput_scalar_le (j : ℤ) (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    (∫ e, ‖correctedKernelHolInput j 0 B e z‖
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤
      higherKernelCompactBound 0 B (B * R ^ 2) * B +
        12 * sqrt B * R * (B + 2 * sqrt B) := by
  have hC := higherKernelCompactBound_nonneg 0 B (B * R ^ 2) (by positivity)
  have hE := lowBand_energy_integrable j B
  have hS := lowBand_sqrt_energy_integrable j B
  have hEm : (∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤ B := by
    by_cases hj : |(j : ℝ)| ≤ B
    · rw [lowBand_integral_energy j hj]
      exact (Real.sqrt_le_left hB).mpr (by nlinarith [sq_nonneg (j : ℝ)])
    · simp [Ioo_eq_empty_of_le (le_of_not_ge hj), hB]
  calc
    _ ≤ ∫ e, scalarColumnMajorant B R e
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
      apply integral_mono_ae (correctedKernelHolInput_scalar_integrable j B hB z).norm
        (scalarColumnMajorant_integrable j B R)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      exact norm_correctedKernelHolInput_scalar_le j B R e z hB hR he.1.le he.2.le hz
    _ = higherKernelCompactBound 0 B (B * R ^ 2) *
        (∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) +
        12 * sqrt B * R *
        (∫ e, sqrt e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
      unfold scalarColumnMajorant
      rw [integral_add (hE.const_mul _) (hS.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hEm hC)
      (mul_le_mul_of_nonneg_left (lowBand_integral_sqrt_energy_le j B hB) (by positivity))

/-- The `MemLp.toLp` representative has the same ordinary mass estimate. -/
theorem norm_correctedKernelHolInput_scalar_toL1_le (j : ℤ) (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(correctedKernelHolInput_scalar_memLp_one j B hB z).toLp
      (fun e : ℝ => correctedKernelHolInput j 0 B e z)‖ ≤
      higherKernelCompactBound 0 B (B * R ^ 2) * B +
        12 * sqrt B * R * (B + 2 * sqrt B) := by
  change ‖(correctedKernelHolInput_scalar_integrable j B hB z).toL1
    (fun e : ℝ => correctedKernelHolInput j 0 B e z)‖ ≤ _
  rw [L1.norm_of_fun_eq_integral_norm]
  exact integral_norm_correctedKernelHolInput_scalar_le j B R hB hR z hz

end GapFamily.Analytic
