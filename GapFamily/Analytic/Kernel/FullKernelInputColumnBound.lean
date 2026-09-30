import GapFamily.Analytic.Kernel.FullKernelResponse
import GapFamily.Analytic.Kernel.FullKernelReality
import GapFamily.Analytic.Kernel.FullKernelInputColumnMoment

/-!
# Arbitrary input column on a complex disk

The input coordinate is `|jin| + z²`. Exchanging the actual full kernel's
input and output keeps an energy factor in the central contribution as well
as the higher contribution. The scalar correction has a square-root energy
factor. Thus the column belongs to ordinary `L¹` and `L²` on every low band.
-/

noncomputable section

open MeasureTheory Real Set

namespace GapFamily.Analytic

/-- One physical-energy majorant for an arbitrary input spin at unit scale. -/
def inputColumnMajorant (jin : ℤ) (B R e : ℝ) : ℝ :=
  fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2) * e + 12 * R * sqrt e

theorem inputColumnMajorant_nonneg (jin : ℤ) (B R e : ℝ)
    (hR : 0 ≤ R) (he : 0 ≤ e) : 0 ≤ inputColumnMajorant jin B R e := by
  have hC := fullKernelCompactBound_nonneg jin B (|(jin : ℝ)| + R ^ 2) (by positivity)
  unfold inputColumnMajorant
  positivity

/-- The majorant retains square integrability at the scalar reference endpoint. -/
theorem inputColumnMajorant_memLp (j jin : ℤ) (B : ℝ) (hB : 0 ≤ B) (R : ℝ) :
    MemLp (inputColumnMajorant jin B R) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  ((lowBand_energy_memLp j B hB).const_mul
    (fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2))).add
    ((lowBand_sqrt_energy_memLp j B).const_mul (12 * R))

theorem inputColumnMajorant_integrable (j jin : ℤ) (B R : ℝ) :
    Integrable (inputColumnMajorant jin B R)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  ((lowBand_energy_integrable j B).const_mul
    (fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2))).add
    ((lowBand_sqrt_energy_integrable j B).const_mul (12 * R))

theorem inputColumnMajorant_memLp_one (j jin : ℤ) (B : ℝ) (_hB : 0 ≤ B) (R : ℝ) :
    MemLp (inputColumnMajorant jin B R) 1
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  memLp_one_iff_integrable.mpr (inputColumnMajorant_integrable j jin B R)

/-- The actual full input column obeys a disk-uniform energy majorant. -/
theorem norm_correctedKernelHolInput_unit_le (j jin : ℤ) (B R e : ℝ) (z : ℂ)
    (hR : 0 ≤ R) (he : |(j : ℝ)| ≤ e) (heB : e ≤ B) (hz : ‖z‖ ≤ R) :
    ‖correctedKernelHolInput j jin 1 e z‖ ≤ inputColumnMajorant jin B R e := by
  have harg : ‖Complex.ofReal |(jin : ℝ)| + z ^ 2‖ ≤ |(jin : ℝ)| + R ^ 2 := by
    calc
      _ ≤ ‖Complex.ofReal |(jin : ℝ)|‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ = |(jin : ℝ)| + ‖z‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (abs_nonneg _), norm_pow]
      _ ≤ _ := by gcongr
  have hfull := norm_fullKernel_complex_output_on_band_le jin j
    (Complex.ofReal |(jin : ℝ)| + z ^ 2) e B (|(jin : ℝ)| + R ^ 2) he heB harg
  have hrank :
      ‖(if j = 0 ∧ jin = 0 then (12 : ℂ) * (sqrt e : ℂ) * z else 0)‖ ≤
        12 * R * sqrt e := by
    split_ifs
    · simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg (sqrt_nonneg _)]
      calc
        12 * sqrt e * ‖z‖ ≤ 12 * sqrt e * R := by gcongr
        _ = _ := by ring
    · simp only [norm_zero]
      positivity
  unfold correctedKernelHolInput
  simp only [Complex.ofReal_one, one_mul, sqrt_one, mul_one]
  rw [fullKernelHol_symm]
  exact (norm_add_le _ _).trans (add_le_add hfull hrank)

/-- Output-energy continuity at every complex unit-scale input coordinate. -/
theorem continuous_correctedKernelHolInput_unit (j jin : ℤ) (z : ℂ) :
    Continuous (fun e : ℝ => correctedKernelHolInput j jin 1 e z) := by
  unfold correctedKernelHolInput
  simp only [Complex.ofReal_one, one_mul, sqrt_one, mul_one]
  apply Continuous.add
  · have hp : Continuous (fun e : ℝ => ((e : ℂ), Complex.ofReal |(jin : ℝ)| + z ^ 2)) := by
      fun_prop
    simpa only [Function.comp_def] using (continuous_fullKernelHol j jin).comp hp
  · split_ifs <;> fun_prop

/-- The full arbitrary-spin complex column is a physical Hilbert row. -/
theorem correctedKernelHolInput_unit_memLp (j jin : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (z : ℂ) :
    MemLp (fun e : ℝ => correctedKernelHolInput j jin 1 e z) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  apply (inputColumnMajorant_memLp j jin B hB ‖z‖).of_le
    (continuous_correctedKernelHolInput_unit j jin z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  rw [Real.norm_of_nonneg (inputColumnMajorant_nonneg jin B ‖z‖ e (norm_nonneg _)
    ((abs_nonneg _).trans he.1.le))]
  exact norm_correctedKernelHolInput_unit_le j jin B ‖z‖ e z (norm_nonneg _)
    he.1.le he.2.le le_rfl

/-- The same column also has finite ordinary reference-measure mass. -/
theorem correctedKernelHolInput_unit_integrable (j jin : ℤ) (B : ℝ)
    (_hB : 0 ≤ B) (z : ℂ) :
    Integrable (fun e : ℝ => correctedKernelHolInput j jin 1 e z)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  apply (inputColumnMajorant_integrable j jin B ‖z‖).mono'
    (continuous_correctedKernelHolInput_unit j jin z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact norm_correctedKernelHolInput_unit_le j jin B ‖z‖ e z (norm_nonneg _)
    he.1.le he.2.le le_rfl

theorem correctedKernelHolInput_unit_memLp_one (j jin : ℤ) (B : ℝ)
    (hB : 0 ≤ B) (z : ℂ) :
    MemLp (fun e : ℝ => correctedKernelHolInput j jin 1 e z) 1
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  memLp_one_iff_integrable.mpr (correctedKernelHolInput_unit_integrable j jin B hB z)

/-- Exact moment bound for the Hilbert column on a fixed complex disk. -/
theorem norm_correctedKernelHolInput_unit_toLp_le (j jin : ℤ) (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(correctedKernelHolInput_unit_memLp j jin B hB z).toLp
      (fun e : ℝ => correctedKernelHolInput j jin 1 e z)‖ ≤
      fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2) * B + 12 * R * sqrt B := by
  have hC := fullKernelCompactBound_nonneg jin B (|(jin : ℝ)| + R ^ 2) (by positivity)
  apply norm_toLp_le_of_energy_sqrt_bound j B hB _ _
    (fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2)) (12 * R) hC (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact norm_correctedKernelHolInput_unit_le j jin B R e z hR he.1.le he.2.le hz

/-- Exact moment bound for the ordinary `L¹` column on a fixed complex disk. -/
theorem norm_correctedKernelHolInput_unit_toL1_le (j jin : ℤ) (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(correctedKernelHolInput_unit_memLp_one j jin B hB z).toLp
      (fun e : ℝ => correctedKernelHolInput j jin 1 e z)‖ ≤
      fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2) * B +
        12 * R * (B + 2 * sqrt B) := by
  have hC := fullKernelCompactBound_nonneg jin B (|(jin : ℝ)| + R ^ 2) (by positivity)
  apply norm_toL1_le_of_energy_sqrt_bound j B hB _ _
    (fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2)) (12 * R) hC (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact norm_correctedKernelHolInput_unit_le j jin B R e z hR he.1.le he.2.le hz

end GapFamily.Analytic
