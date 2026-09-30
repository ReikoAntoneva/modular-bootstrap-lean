import GapFamily.Construction.MarkerReferenceSeed
import GapFamily.Analytic.Poincare.Fourier.PoincareLowBandThermalOutput

/-!
# The actual ordinary thermal reference output

The continuum of the actual four-seed vacuum and the threshold-canceled
reference correction define ordinary signed measures. Their masses are the
actual Fourier coefficients, and their low-band restrictions vanish.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace GapFamily.Construction

open Analytic PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier

private theorem vacuum_laplace_exp (y e : ℝ) :
    Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) =
      (Real.exp (-(2 * Real.pi * y) * e) : ℂ) := by
  rw [show -2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ) =
    ((-(2 * Real.pi * y) * e : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_exp]

/-- The ordinary real thermal density of the actual vacuum continuum. -/
def vacuumThermalDensity (a : ℝ) (j : ℤ) (t e : ℝ) : ℝ :=
  Real.exp (-t * e) * (vacuumFullKernel a e j).re

theorem integrable_vacuumThermalDensity (a : ℝ) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable (vacuumThermalDensity a j t) (referenceMeasure j) := by
  have hi : Integrable (fun e : ℝ =>
      (Complex.exp (-2 * (Real.pi : ℂ) * ((t / (2 * Real.pi) : ℝ) : ℂ) * (e : ℂ)) *
        vacuumFullKernel a e j).re) (referenceMeasure j) :=
    (integrable_vacuumFullKernel_laplace a (t / (2 * Real.pi)) (by positivity) j).re
  have hscale : 2 * Real.pi * (t / (2 * Real.pi)) = t := by
    field_simp
  simpa only [vacuum_laplace_exp, hscale, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, vacuumThermalDensity] using! hi

/-- An ordinary finite signed measure, with no artificial mass at the scalar threshold. -/
def vacuumThermalContinuumMeasure (a : ℝ) (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  (referenceMeasure j).withDensityᵥ (vacuumThermalDensity a j t)

theorem vacuumThermalContinuumMeasure_apply (a : ℝ) (j : ℤ) {t : ℝ} (ht : 0 < t)
    (s : Set ℝ) (hs : MeasurableSet s) :
    vacuumThermalContinuumMeasure a j t s =
      ∫ e in s, vacuumThermalDensity a j t e ∂referenceMeasure j :=
  withDensityᵥ_apply (integrable_vacuumThermalDensity a j ht) hs

@[simp] theorem vacuumThermalContinuumMeasure_singleton (a : ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t) (e : ℝ) : vacuumThermalContinuumMeasure a j t {e} = 0 := by
  rw [vacuumThermalContinuumMeasure_apply a j ht _ (measurableSet_singleton e)]
  simp

theorem vacuumThermalContinuumMeasure_apply_eq_zero_below_edge (a : ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t) (s : Set ℝ) (hs : MeasurableSet s)
    (hbelow : s ⊆ Iic |(j : ℝ)|) : vacuumThermalContinuumMeasure a j t s = 0 := by
  rw [vacuumThermalContinuumMeasure_apply a j ht s hs,
    Measure.restrict_eq_zero.mpr (referenceMeasure_apply_eq_zero_below_edge j s hbelow),
    integral_zero_measure]

/-- Its actual thermal mass is the previously proved full vacuum Laplace integral. -/
theorem vacuumThermalContinuumMeasure_mass (a : ℝ) (j : ℤ)
    (y : ℝ) (hy : 0 < y) :
    (vacuumThermalContinuumMeasure a j (2 * Real.pi * y) univ : ℂ) =
      ∫ e, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        vacuumFullKernel a e j ∂referenceMeasure j := by
  rw [vacuumThermalContinuumMeasure_apply a j (by positivity) univ MeasurableSet.univ,
    Measure.restrict_univ, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with e
  rw [vacuumThermalDensity, Complex.ofReal_mul, vacuum_laplace_exp]
  congr 1
  exact vacuumNumerator_coe_eq a e j

private theorem vacuum_reference_nonnegative (j : ℤ) (b : ℝ) :
    ∀ᵐ e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b), 0 ≤ e := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact (abs_nonneg (j : ℝ)).trans he.1.le

theorem vacuumThermalContinuumMeasure_restrict_lowBand
    (a b : ℝ) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (vacuumThermalContinuumMeasure a j t).restrict (Ioo |(j : ℝ)| b) =
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| b)).withDensityᵥ
        (vacuumThermalDensity a j t) := by
  ext s hs
  rw [VectorMeasure.restrict_apply _ measurableSet_Ioo hs,
    vacuumThermalContinuumMeasure_apply a j ht _ (hs.inter measurableSet_Ioo),
    withDensityᵥ_apply (integrable_vacuumThermalDensity a j ht).restrict hs,
    Measure.restrict_restrict hs]

theorem thermalSignedInputMeasure_neg_vacuumLowBandMeasure
    (a b : ℝ) (j : ℤ) (ha : 2 ≤ a) {t : ℝ} (ht : 0 < t) :
    thermalSignedInputMeasure (-vacuumLowBandMeasure a b j) t =
      -(vacuumThermalContinuumMeasure a j t).restrict (Ioo |(j : ℝ)| b) := by
  rw [vacuumLowBandMeasure, ← withDensityᵥ_neg']
  change (((referenceMeasure j).restrict (Ioo |(j : ℝ)| b)).withDensityᵥ
    (fun e => -(vacuumFullKernel a e j).re)).withDensity _ _ = _
  have hneg : Integrable (fun e => -(vacuumFullKernel a e j).re)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| b)) :=
    (vacuumFullKernel_lowBand_integrable a b j ha).re.neg
  rw [signedDensity_withDensity_thermal
    hneg
    (vacuum_reference_nonnegative j b) ht.le,
    vacuumThermalContinuumMeasure_restrict_lowBand a b j ht]
  simp only [mul_neg, withDensityᵥ_neg']
  rfl

variable (S : Finset ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 < b)
  (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))

/-- The complete actual reference output after its prescribed direct vacuum is removed. -/
def markerReferenceThermalMeasure (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  vacuumThermalContinuumMeasure a j t + markerReferenceNonthresholdOutput S a b ha hb hunit j t

/-- The full actual reference output has exactly its unit scalar marker and no other atom. -/
theorem markerReferenceThermalMeasure_singleton (h0 : 0 ∈ S)
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    markerReferenceThermalMeasure S a b ha hb hunit j t {e} =
      if j = 0 ∧ e = b then Real.exp (-t * e) else 0 := by
  rw [markerReferenceThermalMeasure, _root_.add_apply,
    vacuumThermalContinuumMeasure_singleton a j ht e, zero_add,
    markerReferenceNonthresholdOutput_singleton S a b ha hb hunit h0 j ht e]

/-- The scalar atom has already canceled, so the Fourier coefficient is the actual signed mass. -/
theorem markerReferenceOutputCoefficient_eq_thermalMass
    (y : ℝ) (hy : 0 < y) (j : ℤ) :
    markerReferenceOutputCoefficient S a b ha hb hunit y j =
      (Real.sqrt y : ℂ) *
        (markerReferenceThermalMeasure S a b ha hb hunit j (2 * Real.pi * y) univ : ℂ) := by
  rw [markerReferenceOutputCoefficient, ← vacuumThermalContinuumMeasure_mass a j y hy]
  simp only [markerReferenceThermalMeasure, _root_.add_apply, Complex.ofReal_add, mul_add]

theorem hasSum_markerReferenceSeed_thermalMeasure (h0 : 0 ∈ S)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (markerReferenceThermalMeasure S a b ha hb hunit j (2 * Real.pi * y) univ : ℂ) *
        cuspFourierMode j x)
      (markerReferenceSeed S a b ha hb hunit (rowPoint y hy x) - vacuumDirectRow a y x) := by
  simpa only [markerReferenceOutputCoefficient_eq_thermalMass S a b ha hb hunit y hy] using
    hasSum_markerReferenceSeed_output S a b ha hb hunit h0 y hy x

/-- Exact cancellation on the ordinary thermal open low band. -/
theorem markerReferenceThermalMeasure_restrict_openLowBand
    (h0 : 0 ∈ S) (j : ℤ) (hj : j ∈ S) {t : ℝ} (ht : 0 < t) :
    (markerReferenceThermalMeasure S a b ha hb hunit j t).restrict (Ioo |(j : ℝ)| b) = 0 := by
  have hnon : (markerReferenceNonthresholdOutput S a b ha hb hunit j t).restrict
        (Ioo |(j : ℝ)| b) =
      (correctedThermalFiniteOutputMeasure S (markerReferenceInput S a b ha hb hunit)
        j t).restrict (Ioo |(j : ℝ)| b) := by
    rw [markerReferenceThermalOutput_eq S a b ha hb hunit h0 j t,
      VectorMeasure.restrict_add]
    have hz : (0 : ℝ) ∉ Ioo |(j : ℝ)| b := fun h =>
      (not_lt_of_ge (abs_nonneg (j : ℝ))) h.1
    split_ifs <;> simp only [VectorMeasure.restrict_dirac_of_notMem hz,
      VectorMeasure.restrict_zero, add_zero]
  rw [markerReferenceThermalMeasure, VectorMeasure.restrict_add, hnon,
    correctedThermalFiniteOutputMeasure_restrict_lowBand S _ j (3 * b) b
      (markerReferenceInput_physicalSupport S a b ha hb hunit) ht,
    markerReferenceInput_lowBandOutput S a b ha hb hunit h0 j hj,
    thermalSignedInputMeasure_neg_vacuumLowBandMeasure a b j ha ht, add_neg_cancel]

end GapFamily.Construction
