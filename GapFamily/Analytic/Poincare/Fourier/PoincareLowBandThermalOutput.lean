import GapFamily.Analytic.Poincare.Fourier.PoincareLowBandOutput
import GapFamily.Analytic.Foundation.SignedThermalDensity

/-! Restricting the actual thermal output to the open low band retains the
direct input and the ordinary corrected response. The separately tracked
scalar threshold atom vanishes under this restriction.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set
open scoped Classical BigOperators

/-- The literal row output on the open band has precisely its tilted direct
input and its restricted ordinary thermal density. -/
theorem correctedThermalRowOutputMeasure_restrict_lowBand
    (ν : SignedMeasure ℝ) (J j : ℤ) (M B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    {t : ℝ} (ht : 0 < t) :
    (correctedThermalRowOutputMeasure ν J j t).restrict (Ioo |(j : ℝ)| B) =
      (if j = J then thermalSignedInputMeasure (ν.restrict (Ioo |(j : ℝ)| B)) t else 0) +
        ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)).withDensityᵥ
          (correctedThermalRowDensity ν J j t) := by
  have h0 : (0 : ℝ) ∉ Ioo |(j : ℝ)| B := fun h =>
    (not_lt_of_ge (abs_nonneg (j : ℝ))) h.1
  have hc : (correctedThermalContinuumMeasure ν J j t).restrict (Ioo |(j : ℝ)| B) =
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)).withDensityᵥ
        (correctedThermalRowDensity ν J j t) := by
    ext s hset
    rw [VectorMeasure.restrict_apply _ measurableSet_Ioo hset,
      correctedThermalContinuumMeasure_apply ν J j M hs ht _ (hset.inter measurableSet_Ioo),
      withDensityᵥ_apply (integrable_correctedThermalRowDensity ν J j M hs ht).restrict hset,
      Measure.restrict_restrict hset]
  simp only [correctedThermalRowOutputMeasure, VectorMeasure.restrict_add]
  rw [hc]
  have hd : (thermalSignedInputMeasure ν t).restrict (Ioo |(j : ℝ)| B) =
      thermalSignedInputMeasure (ν.restrict (Ioo |(j : ℝ)| B)) t :=
    VectorMeasure.restrict_withDensity (signedIntegrable_thermalInput ν J M hs ht)
  have ha : (if j = 0 then VectorMeasure.dirac (0 : ℝ)
      ((PoincareScalarFourier.scalarThresholdCoefficient J).re * ν univ) else 0).restrict
      (Ioo |(j : ℝ)| B) = 0 := by
    split_ifs <;> simp only [VectorMeasure.restrict_dirac_of_notMem h0,
      VectorMeasure.restrict_zero]
  rw [ha, add_zero]
  split_ifs <;> simp only [hd, VectorMeasure.restrict_zero]

/-- Ordinary integrability of the finite corrected thermal density follows
from the actual compact physical input rows. -/
theorem integrable_finiteCorrectedThermalDensity
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (M : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun e => Real.exp (-t * e) *
      (correctedSignedResponse (fun J : S => ν J) (fun J : S => (J : ℤ)) j e).re)
      (referenceMeasure j) := by
  have hi := integrable_finsetSum S (fun J hJ =>
    integrable_correctedThermalRowDensity (ν J) J j M (hs J hJ) ht)
  convert hi using 1
  funext e
  simp only [correctedSignedResponse, Complex.re_sum, Finset.mul_sum,
    correctedThermalRowDensity]
  exact Finset.sum_coe_sort S (fun J => Real.exp (-t * e) *
    (correctedSignedRowResponse (ν J) J j e).re)

/-- Finite thermal superposition has the same direct and induced density on
every open low band, with no residual threshold mass. -/
theorem correctedThermalFiniteOutputMeasure_restrict_lowBand_density
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (M B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure S ν j t).restrict (Ioo |(j : ℝ)| B) =
      (if j ∈ S then thermalSignedInputMeasure ((ν j).restrict (Ioo |(j : ℝ)| B)) t else 0) +
        ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)).withDensityᵥ
          (fun e => Real.exp (-t * e) *
            (correctedSignedResponse (fun J : S => ν J) (fun J : S => (J : ℤ)) j e).re) := by
  have hr : (correctedThermalFiniteOutputMeasure S ν j t).restrict (Ioo |(j : ℝ)| B) =
      ∑ J ∈ S, (correctedThermalRowOutputMeasure (ν J) J j t).restrict (Ioo |(j : ℝ)| B) := by
    exact map_sum (VectorMeasure.restrictGm (Ioo |(j : ℝ)| B)) _ S
  rw [hr]
  rw [Finset.sum_congr rfl (fun J hJ =>
    correctedThermalRowOutputMeasure_restrict_lowBand (ν J) J j M B (hs J hJ) ht)]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.sum_ite_eq]
  · ext s hset
    simp only [_root_.sum_apply]
    rw [withDensityᵥ_apply (integrable_finiteCorrectedThermalDensity S ν j M hs ht).restrict hset]
    rw [Finset.sum_congr rfl (fun J hJ =>
      withDensityᵥ_apply (integrable_correctedThermalRowDensity (ν J) J j M (hs J hJ) ht).restrict hset)]
    rw [← integral_finsetSum S (fun J hJ =>
      (integrable_correctedThermalRowDensity (ν J) J j M (hs J hJ) ht).restrict.restrict)]
    apply integral_congr_ae
    filter_upwards with e
    simp only [correctedSignedResponse, Complex.re_sum, Finset.mul_sum,
      correctedThermalRowDensity]
    exact (Finset.sum_coe_sort S (fun J => Real.exp (-t * e) *
      (correctedSignedRowResponse (ν J) J j e).re)).symm

/-- Thermal tilting multiplies the actual ordinary corrected low-band density
by the exponential, with ordinary integrability already established. -/
theorem thermalSignedInputMeasure_correctedSignedOutputMeasure
    {ι : Type*} [Fintype ι] (ν : ι → SignedMeasure ℝ) (J : ι → ℤ)
    (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    {t : ℝ} (ht : 0 < t) :
    thermalSignedInputMeasure (correctedSignedOutputMeasure ν J j M B hs) t =
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)).withDensityᵥ
        (fun e => Real.exp (-t * e) * (correctedSignedResponse ν J j e).re) := by
  have hpos : ∀ᵐ E ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B), 0 ≤ E := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
    exact (abs_nonneg (j : ℝ)).trans hE.1.le
  rw [correctedSignedOutputMeasure_eq_withDensity]
  exact signedDensity_withDensity_thermal
    (correctedSignedResponse_integrable_lowBand ν J j M B hs).re hpos ht.le

/-- The actual thermal output, restricted to the open low band, is exactly
the thermal tilt of the actual unweighted low-band output. Compact physical
input and a positive thermal parameter suffice; no output identity is assumed. -/
theorem correctedThermalFiniteOutputMeasure_restrict_lowBand
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (M B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure S ν j t).restrict (Ioo |(j : ℝ)| B) =
      thermalSignedInputMeasure (finiteCorrectedLowBandOutput S ν j M B hs) t := by
  rw [correctedThermalFiniteOutputMeasure_restrict_lowBand_density S ν j M B hs ht]
  have hd : ∀ᵐ E ∂(if j ∈ S then (ν j).restrict (Ioo |(j : ℝ)| B) else 0).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ B := by
    by_cases hj : j ∈ S
    · simp only [hj, ite_true, VectorMeasure.variation_restrict measurableSet_Ioo]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
      exact ⟨hE.1.le, hE.2.le⟩
    · simp [hj]
  unfold finiteCorrectedLowBandOutput
  rw [thermalSignedInputMeasure_add _ _ j B hd
    (correctedSignedOutputMeasure_physicalSupport (fun J : S => ν J) Subtype.val j M B
      (fun J => hs J J.property)) ht,
    thermalSignedInputMeasure_correctedSignedOutputMeasure _ _ _ _ _ _ ht]
  congr 1
  by_cases hj : j ∈ S <;> simp [hj, thermalSignedInputMeasure]

end GapFamily.Analytic
