import GapFamily.Construction.MarkerReferenceOutputSupport

/-! The actual reference output has summable thermal total variation over all
integer spins. This controls the ordinary signed measures themselves, including
possible cancellation inside their Fourier coefficients. -/

noncomputable section

open MeasureTheory Set

namespace GapFamily.Construction

open Analytic PoincareEnergyFourier

theorem vacuumThermalContinuumMeasure_totalVariation
    (a : ℝ) (j : ℤ) (y : ℝ) (hy : 0 < y) :
    (vacuumThermalContinuumMeasure a j (2 * Real.pi * y)).variation.real univ =
      ∫ e, ‖Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        vacuumFullKernel a e j‖ ∂referenceMeasure j := by
  rw [vacuumThermalContinuumMeasure,
    signedDensity_totalVariation (integrable_vacuumThermalDensity a j (by positivity))]
  apply integral_congr_ae
  filter_upwards [] with e
  rw [← Real.norm_eq_abs, ← Complex.norm_real, vacuumThermalDensity, Complex.ofReal_mul]
  have hr : ((vacuumFullKernel a e j).re : ℂ) = vacuumFullKernel a e j :=
    vacuumNumerator_coe_eq a e j
  rw [hr, Complex.ofReal_exp]
  congr 3
  push_cast
  ring

theorem summable_vacuumThermalContinuumMeasure_totalVariation
    (a : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => (vacuumThermalContinuumMeasure a j t).variation.real univ) := by
  have hy : 0 < t / (2 * Real.pi) := by positivity
  have heq : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
  simpa only [← vacuumThermalContinuumMeasure_totalVariation a _ _ hy, heq] using
    summable_integral_norm_vacuumFullKernel_laplace a (t / (2 * Real.pi)) hy

private theorem variation_add_mass_le (ν μ : SignedMeasure ℝ) :
    (ν + μ).variation.real univ ≤ ν.variation.real univ + μ.variation.real univ := by
  let := signedMeasure_isFiniteMeasure_variation ν
  let := signedMeasure_isFiniteMeasure_variation μ
  have hle := (VectorMeasure.variation_add_le (μ := ν) (ν := μ)) univ
  rw [Measure.add_apply] at hle
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
    hle).trans_eq (ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _))

variable (S : Finset ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 < b)
  (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))

theorem summable_markerReferenceNonthresholdOutput_totalVariation
    (h0 : 0 ∈ S) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ =>
      (markerReferenceNonthresholdOutput S a b ha hb hunit j t).variation.real univ) := by
  apply (summable_correctedThermalFiniteOutputMeasure_totalVariation S
    (markerReferenceInput S a b ha hb hunit) (3 * b)
    (markerReferenceInput_physicalSupport S a b ha hb hunit) ht).congr_cofinite
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with j hj
  rw [markerReferenceThermalOutput_eq S a b ha hb hunit h0 j t, ite_eq_right hj, add_zero]

/-- Absolute thermal summability holds for the actual ordinary output measures. -/
theorem summable_markerReferenceThermalMeasure_totalVariation
    (h0 : 0 ∈ S) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ =>
      (markerReferenceThermalMeasure S a b ha hb hunit j t).variation.real univ) := by
  apply ((summable_vacuumThermalContinuumMeasure_totalVariation a ht).add
    (summable_markerReferenceNonthresholdOutput_totalVariation S a b ha hb hunit h0 ht)).of_nonneg_of_le
      (fun _ => ENNReal.toReal_nonneg)
  intro j
  exact variation_add_mass_le _ _

/-- The canonical reference has finite total thermal variation across the entire spin lattice. -/
theorem summable_canonicalMarkerReferenceThermalMeasure_totalVariation
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ =>
      (canonicalMarkerReferenceThermalMeasure a b ha hb j t).variation.real univ) :=
  summable_markerReferenceThermalMeasure_totalVariation (lowBandSpinSet b) a b ha
    (by linarith) (isUnit_correctedLowBandIdentityPlus_canonical b hb)
    (by simpa using zero_lt_one.trans_le hb) ht

end GapFamily.Construction
