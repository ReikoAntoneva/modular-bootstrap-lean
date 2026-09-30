import GapFamily.Analytic.Kernel.FullKernelScalarAnchorPhysicalBound
import GapFamily.Analytic.Foundation.ThresholdAnchorBandBound

/-! Ordinary quantitative bounds for the actual normalized high-band anchor.
The actual spatial positivity discharges the inverse hypothesis, and the
actual response square mass supplies the normalization denominator. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Real

/-- The response and reciprocal normalization rates add. -/
def scalarAnchorMeasureBaseExponent : ℝ :=
  scalarAnchorResponseDiskExponent 2 + scalarAnchorResponseMassExponent

/-- One rate controls the ordinary mass, half-energy moment, and numerator. -/
def scalarAnchorMeasureExponent : ℝ := scalarAnchorMeasureBaseExponent + 4

theorem scalarAnchorMeasureBaseExponent_pos : 0 < scalarAnchorMeasureBaseExponent := by
  unfold scalarAnchorMeasureBaseExponent
  have := scalarAnchorResponseDiskExponent_pos 2 (by norm_num)
  have := scalarAnchorResponseMassExponent_pos
  positivity

theorem scalarAnchorMeasureExponent_pos : 0 < scalarAnchorMeasureExponent := by
  unfold scalarAnchorMeasureExponent
  have := scalarAnchorMeasureBaseExponent_pos
  positivity

variable {ι : Type*} [Fintype ι]

/-- The genuine normalization ratio is controlled by the proved response and
reciprocal square-mass estimates. -/
theorem scalarAnchorBand_actual_ratio_le_exp
    (J : ι → ℤ) (hJ : Function.Injective J) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) :
    exp (scalarAnchorResponseDiskExponent 2 * B) /
      scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith)) ≤
        exp (scalarAnchorMeasureBaseExponent * B) := by
  rw [div_eq_mul_inv]
  calc
    _ ≤ exp (scalarAnchorResponseDiskExponent 2 * B) *
        exp (scalarAnchorResponseMassExponent * B) :=
      mul_le_mul_of_nonneg_left
        (scalarAnchorResponseSquareMass_inv_le_exp J hJ B hB hband) (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; unfold scalarAnchorMeasureBaseExponent; ring

private theorem scalarAnchor_exp_base_le {B : ℝ} (hB : 0 ≤ B) :
    exp (scalarAnchorMeasureBaseExponent * B) ≤ exp (scalarAnchorMeasureExponent * B) := by
  apply exp_le_exp.mpr
  unfold scalarAnchorMeasureExponent
  nlinarith

/-- The literal zero-extended numerator is uniformly exponentially bounded. -/
theorem abs_scalarAnchorNumerator_actual_le_exp
    (J : ι → ℤ) (hJ : Function.Injective J) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) (E : ℝ) :
    |scalarAnchorNumerator B (scalarAnchorResponsePhysical J B (by linarith)) E| ≤
      exp (scalarAnchorMeasureExponent * B) := by
  have hI := scalarAnchorResponseSquareMass_pos J hJ B hB hband
  exact (abs_scalarAnchorNumerator_le B
    (scalarAnchorResponsePhysical J B (by linarith))
    (exp (scalarAnchorResponseDiskExponent 2 * B)) (exp_pos _).le hI
    (abs_scalarAnchorResponsePhysical_le_exp J hJ B hB hband) E).trans
      ((scalarAnchorBand_actual_ratio_le_exp J hJ B hB hband).trans
        (scalarAnchor_exp_base_le (by linarith)))

/-- The total variation is that of the actual ordinary high-band signed measure. -/
theorem scalarAnchorBandMeasure_actual_totalVariation_le_exp
    (J : ι → ℤ) (hJ : Function.Injective J) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) :
    (scalarAnchorBandMeasure B (by linarith)
      (scalarAnchorResponsePhysical J B (by linarith))
      (continuous_scalarAnchorResponsePhysical J B (by linarith)).continuousOn).variation.real univ ≤
        exp (scalarAnchorMeasureExponent * B) := by
  have hI := scalarAnchorResponseSquareMass_pos J hJ B hB hband
  calc
    _ ≤ exp (scalarAnchorResponseDiskExponent 2 * B) /
        (2 * scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith))) :=
      scalarAnchorBandMeasure_totalVariation_le B (by linarith)
        (scalarAnchorResponsePhysical J B (by linarith))
        (continuous_scalarAnchorResponsePhysical J B (by linarith)).continuousOn
        (exp (scalarAnchorResponseDiskExponent 2 * B)) (exp_pos _).le hI
        (abs_scalarAnchorResponsePhysical_le_exp J hJ B hB hband)
    _ ≤ exp (scalarAnchorResponseDiskExponent 2 * B) /
        scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith)) := by
      apply div_le_div_of_nonneg_left (exp_pos _).le hI
      linarith
    _ ≤ exp (scalarAnchorMeasureBaseExponent * B) :=
      scalarAnchorBand_actual_ratio_le_exp J hJ B hB hband
    _ ≤ _ := scalarAnchor_exp_base_le (by linarith)

/-- The ordinary half-energy moment of the same signed measure has the same rate. -/
theorem scalarAnchorBandMeasure_actual_sqrt_integral_le_exp
    (J : ι → ℤ) (hJ : Function.Injective J) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) :
    (∫ E, sqrt E ∂(scalarAnchorBandMeasure B (by linarith)
      (scalarAnchorResponsePhysical J B (by linarith))
      (continuous_scalarAnchorResponsePhysical J B (by linarith)).continuousOn).variation) ≤
        exp (scalarAnchorMeasureExponent * B) := by
  have hI := scalarAnchorResponseSquareMass_pos J hJ B hB hband
  have hs : sqrt (3 * B) ≤ 3 * B := sqrt_le_self_iff.mpr (Or.inr (by linarith))
  calc
    _ ≤ sqrt (3 * B) * exp (scalarAnchorResponseDiskExponent 2 * B) /
        (2 * scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith))) :=
      scalarAnchorBandMeasure_sqrt_integral_le B (by linarith)
        (scalarAnchorResponsePhysical J B (by linarith))
        (continuous_scalarAnchorResponsePhysical J B (by linarith)).continuousOn
        (exp (scalarAnchorResponseDiskExponent 2 * B)) (exp_pos _).le hI
        (abs_scalarAnchorResponsePhysical_le_exp J hJ B hB hband)
    _ ≤ sqrt (3 * B) * exp (scalarAnchorResponseDiskExponent 2 * B) /
        scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith)) := by
      apply div_le_div_of_nonneg_left (by positivity) hI
      linarith
    _ = sqrt (3 * B) * (exp (scalarAnchorResponseDiskExponent 2 * B) /
        scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith))) := by ring
    _ ≤ (3 * B) * exp (scalarAnchorMeasureBaseExponent * B) :=
      mul_le_mul hs (scalarAnchorBand_actual_ratio_le_exp J hJ B hB hband)
        (div_nonneg (exp_pos _).le hI.le) (by linarith)
    _ ≤ _ := by
      convert polynomial_mul_exp_le_exp (A := (3 : ℝ))
        (D := scalarAnchorMeasureBaseExponent) (by norm_num) hB 1 using 1 <;>
        simp only [pow_one, Nat.cast_one]
      congr 1
      unfold scalarAnchorMeasureExponent
      ring

end GapFamily.Analytic
