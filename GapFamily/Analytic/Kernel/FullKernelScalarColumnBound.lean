import GapFamily.Analytic.Kernel.FullKernelExtension
import GapFamily.Analytic.Kernel.FullKernelReality
import GapFamily.Analytic.Kernel.HigherKernelResponseBound
import GapFamily.Analytic.Kernel.FullKernelSmoothingMoment
import GapFamily.Analytic.Kernel.FullKernelScalarColumnMoment

/-!
# Scalar column majorant on a complex disk

The actual input column has an energy zero in its higher-kernel part and a
square-root energy zero in the scalar rank correction. Their sum is an
ordinary `L²` majorant even for the scalar measure `de/e`.
-/

noncomputable section

open MeasureTheory Real Set

namespace GapFamily.Analytic

/-- One spin-independent energy majorant for the scalar column on `‖z‖ ≤ R`. -/
def scalarColumnMajorant (B R e : ℝ) : ℝ :=
  higherKernelCompactBound 0 B (B * R ^ 2) * e + 12 * sqrt B * R * sqrt e

theorem scalarColumnMajorant_nonneg (B R e : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (he : 0 ≤ e) :
    0 ≤ scalarColumnMajorant B R e := by
  have hC := higherKernelCompactBound_nonneg 0 B (B * R ^ 2) (by positivity)
  unfold scalarColumnMajorant
  positivity

/-- The same real majorant is square-integrable on every physical low band. -/
theorem scalarColumnMajorant_memLp (j : ℤ) (B : ℝ) (hB : 0 ≤ B) (R : ℝ) :
    MemLp (scalarColumnMajorant B R) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  exact ((lowBand_energy_memLp j B hB).const_mul
    (higherKernelCompactBound 0 B (B * R ^ 2))).add
    ((lowBand_sqrt_energy_memLp j B).const_mul (12 * sqrt B * R))

/-- Uniform pointwise bound for the actual scalar input column. -/
theorem norm_correctedKernelHolInput_scalar_le (j : ℤ) (B R e : ℝ) (z : ℂ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (he : |(j : ℝ)| ≤ e) (heB : e ≤ B)
    (hz : ‖z‖ ≤ R) :
    ‖correctedKernelHolInput j 0 B e z‖ ≤ scalarColumnMajorant B R e := by
  have harg : ‖(B : ℂ) * z ^ 2‖ ≤ B * R ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hB]
    gcongr
  have hhigh := norm_higherKernel_complex_output_on_band_le 0 j
    ((B : ℂ) * z ^ 2) e B (B * R ^ 2) he heB harg
  have hrank :
      ‖(if j = 0 ∧ (0 : ℤ) = 0 then
        (12 : ℂ) * (sqrt e : ℂ) * (sqrt B : ℂ) * z else 0)‖ ≤
        12 * sqrt B * R * sqrt e := by
    split_ifs
    · simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg (sqrt_nonneg _)]
      calc
        12 * sqrt e * sqrt B * ‖z‖ ≤ 12 * sqrt e * sqrt B * R := by gcongr
        _ = _ := by ring
    · simp only [norm_zero]
      positivity
  unfold correctedKernelHolInput
  simp only [Int.cast_zero, abs_zero, Complex.ofReal_zero, zero_add]
  rw [fullKernelHol_symm, fullKernelHol, centralKernel_scalar_output, zero_add]
  exact (norm_add_le _ _).trans (add_le_add hhigh (by simpa only [eq_self] using hrank))

/-- Ordinary continuity in output energy at every complex input coordinate. -/
theorem continuous_correctedKernelHolInput_scalar (j : ℤ) (B : ℝ) (z : ℂ) :
    Continuous (fun e : ℝ => correctedKernelHolInput j 0 B e z) := by
  unfold correctedKernelHolInput
  simp only [Int.cast_zero, abs_zero, Complex.ofReal_zero, zero_add]
  apply Continuous.add
  · have hp : Continuous (fun e : ℝ => ((e : ℂ), (B : ℂ) * z ^ 2)) := by fun_prop
    simpa only [Function.comp_def] using (continuous_fullKernelHol j 0).comp hp
  · split_ifs <;> fun_prop

/-- Every scalar complex input column is an ordinary physical `L²` row. -/
theorem correctedKernelHolInput_scalar_memLp (j : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (z : ℂ) :
    MemLp (fun e : ℝ => correctedKernelHolInput j 0 B e z) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  apply (scalarColumnMajorant_memLp j B hB ‖z‖).of_le
    (continuous_correctedKernelHolInput_scalar j B z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  rw [Real.norm_of_nonneg (scalarColumnMajorant_nonneg B ‖z‖ e hB (norm_nonneg _)
    ((abs_nonneg _).trans he.1.le))]
  exact norm_correctedKernelHolInput_scalar_le j B ‖z‖ e z hB (norm_nonneg _)
    he.1.le he.2.le le_rfl

/-- The majorant controls the Hilbert norm uniformly on the complex disk. -/
theorem norm_correctedKernelHolInput_scalar_toLp_le (j : ℤ) (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(correctedKernelHolInput_scalar_memLp j B hB z).toLp
      (fun e : ℝ => correctedKernelHolInput j 0 B e z)‖ ≤
      higherKernelCompactBound 0 B (B * R ^ 2) * B + 12 * B * R := by
  have hC := higherKernelCompactBound_nonneg 0 B (B * R ^ 2) (by positivity)
  calc
    _ ≤ higherKernelCompactBound 0 B (B * R ^ 2) * B +
        (12 * sqrt B * R) * sqrt B := by
      apply norm_toLp_le_of_energy_sqrt_bound j B hB _ _
        (higherKernelCompactBound 0 B (B * R ^ 2)) (12 * sqrt B * R)
        hC (by positivity)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      exact norm_correctedKernelHolInput_scalar_le j B R e z hB hR he.1.le he.2.le hz
    _ = higherKernelCompactBound 0 B (B * R ^ 2) * B +
        12 * (sqrt B) ^ 2 * R := by ring
    _ = _ := by rw [Real.sq_sqrt hB]

end GapFamily.Analytic
