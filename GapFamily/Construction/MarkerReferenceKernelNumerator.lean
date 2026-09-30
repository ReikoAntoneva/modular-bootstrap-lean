import GapFamily.Construction.MarkerReferenceCanonical
import GapFamily.Construction.MarkerReferenceBound
import GapFamily.Analytic.Foundation.FullVacuumReality
import GapFamily.Analytic.Kernel.FullKernelSignedResponseBound

/-! The actual reference numerator contributed by the vacuum and the full
signed kernel response. Outside the compact direct input this is the whole
ordinary density. -/

noncomputable section

open MeasureTheory Set Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The literal full vacuum plus the response of the canonical signed input. -/
def canonicalMarkerReferenceKernelNumerator (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (j : ℤ) (e : ℝ) : ℝ :=
  Analytic.vacuumNumerator a e j + (correctedSignedResponse
    (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
      Subtype.val j e).re

/-- Every finite physical output band has ordinary absolute mass, including
its scalar endpoint. -/
theorem canonicalMarkerReferenceKernelNumerator_integrable (a b W : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) :
    Integrable (canonicalMarkerReferenceKernelNumerator a b ha hb j)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| W)) :=
  (vacuumFullKernel_lowBand_integrable a W j ha).re.add
    (correctedSignedResponse_integrable_lowBand
      (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
      Subtype.val j (3 * b) W
      (fun J => canonicalMarkerReferenceInput_physicalSupport a b ha hb J)).re

/-- The pointwise exterior error is the genuine full-vacuum remainder plus
the ordinary signed kernel response controlled by the actual input variation. -/
theorem abs_canonicalMarkerReferenceKernelNumerator_sub_le
    (a b e : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ)
    (he : |(j : ℝ)| ≤ e) (hbe : b ≤ e) :
    |canonicalMarkerReferenceKernelNumerator a b ha hb j e - vacuumLeading a e j| ≤
      ‖vacuumFullRemainder a e j‖ +
        signedSeedMass (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) *
          (6 * correctedKernelBound * b * e) := by
  unfold canonicalMarkerReferenceKernelNumerator
  calc
    _ = |(Analytic.vacuumNumerator a e j - vacuumLeading a e j) +
        (correctedSignedResponse
          (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
          Subtype.val j e).re| := by congr 1; ring
    _ ≤ |Analytic.vacuumNumerator a e j - vacuumLeading a e j| +
        |(correctedSignedResponse
          (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
          Subtype.val j e).re| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_vacuumNumerator_sub_eq_norm]
      exact add_le_add le_rfl ((Complex.abs_re_le_norm _).trans
        (norm_correctedSignedResponse_le_exterior
          (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
          Subtype.val j b hb
          (fun J => canonicalMarkerReferenceInput_physicalSupport a b ha hb J) e he hbe))

/-- A local ordinary mass estimate keeps input and output scales separate. -/
theorem integral_abs_canonicalMarkerReferenceKernelNumerator_le
    (a b W : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hW : 0 ≤ W) (j : ℤ) :
    (∫ e, |canonicalMarkerReferenceKernelNumerator a b ha hb j e|
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| W)) ≤
      markerReferenceEnergyBound a W * W +
        signedSeedMass (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) *
          correctedKernelBound * (3 * b * W + sqrt (3 * b) * (W + 2 * sqrt W)) := by
  have hiV := (vacuumFullKernel_lowBand_integrable a W j ha).norm
  have hiR := (correctedSignedResponse_integrable_lowBand
    (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
    Subtype.val j (3 * b) W
    (fun J => canonicalMarkerReferenceInput_physicalSupport a b ha hb J)).norm
  have hVac : (∫ e, ‖vacuumFullKernel a e j‖
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| W)) ≤
        markerReferenceEnergyBound a W * W := by
    have hiE := (lowBand_energy_integrable j W).const_mul (markerReferenceEnergyBound a W)
    calc
      _ ≤ ∫ e, markerReferenceEnergyBound a W * e
          ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| W) := by
        apply integral_mono_ae hiV hiE
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
        exact norm_vacuumFullKernel_lowBand_le a W e j ha he.1.le he.2.le
      _ = markerReferenceEnergyBound a W * ∫ e, e
          ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| W) := integral_const_mul _ _
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (markerReferenceEnergyBound_nonneg a W (by linarith))
        by_cases hj : |(j : ℝ)| ≤ W
        · rw [lowBand_integral_energy j hj]
          exact (sqrt_le_left hW).mpr (by nlinarith [sq_nonneg (j : ℝ)])
        · simp [Ioo_eq_empty_of_le (le_of_not_ge hj), hW]
  calc
    _ ≤ ∫ e, ‖vacuumFullKernel a e j‖ + ‖correctedSignedResponse
        (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) Subtype.val j e‖
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| W) := by
      apply integral_mono_ae (canonicalMarkerReferenceKernelNumerator_integrable a b W ha hb j).abs
        (hiV.add hiR)
      exact Filter.Eventually.of_forall fun e => (abs_add_le _ _).trans
        (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _))
    _ = (∫ e, ‖vacuumFullKernel a e j‖ ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| W)) +
        ∫ e, ‖correctedSignedResponse
          (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) Subtype.val j e‖
          ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| W) := integral_add hiV hiR
    _ ≤ _ := add_le_add hVac (integral_norm_correctedSignedResponse_lowBand_le
      _ Subtype.val j (3 * b) W (by linarith) hW
      (fun J => canonicalMarkerReferenceInput_physicalSupport a b ha hb J))

end GapFamily.Construction
