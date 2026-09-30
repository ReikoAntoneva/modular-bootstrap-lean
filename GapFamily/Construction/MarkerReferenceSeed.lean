import GapFamily.Construction.MarkerReferenceInput
import GapFamily.Analytic.Foundation.FullVacuumOutput
import GapFamily.Analytic.Poincare.Fourier.PoincareSignedOutputMeasure
import GapFamily.Analytic.Poincare.Fourier.PoincarePhysicalOutputSupport

/-!
# The actual modular marker reference seed

The complete reference function is the actual four-seed vacuum plus the
corrected signed superposition of its constructed marker reference input.
Its threshold mass cancels the vacuum's scalar atom, leaving the ordinary
continuum and the one prescribed scalar marker.
-/

noncomputable section

open MeasureTheory Set UpperHalfPlane
open scoped Classical BigOperators MatrixGroups

namespace GapFamily.Construction

open Analytic PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier

variable (S : Finset ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 < b)
  (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))

/-- The literal modular vacuum plus its constructed signed reference correction. -/
def markerReferenceSeed (τ : UpperHalfPlane) : ℂ :=
  vacuumReducedSeed a τ +
    correctedSeedSuperposition S (markerReferenceInput S a b ha hb hunit) τ

/-- Modularity follows from the actual constituent Poincaré seeds. -/
theorem markerReferenceSeed_smul (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    markerReferenceSeed S a b ha hb hunit (g • τ) =
      markerReferenceSeed S a b ha hb hunit τ := by
  simp only [markerReferenceSeed, vacuumReducedSeed_smul, correctedSeedSuperposition_smul]

theorem continuous_markerReferenceSeed : Continuous (markerReferenceSeed S a b ha hb hunit) :=
  (continuous_vacuumReducedSeed a).add
    (continuous_correctedSeedSuperposition S _ (3 * b)
      (markerReferenceInput_physicalSupport S a b ha hb hunit))

/-- The actual thermally tilted direct input and induced ordinary continuum,
with the separately identified scalar threshold atom omitted. -/
def markerReferenceNonthresholdOutput (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  (if j ∈ S then thermalSignedInputMeasure (markerReferenceInput S a b ha hb hunit j) t else 0) +
    ∑ J ∈ S, correctedThermalContinuumMeasure (markerReferenceInput S a b ha hb hunit J) J j t

/-- The actual correction's scalar threshold is precisely the six units needed by the vacuum. -/
theorem markerReferenceThermalOutput_eq (h0 : 0 ∈ S)
    (j : ℤ) (t : ℝ) :
    correctedThermalFiniteOutputMeasure S (markerReferenceInput S a b ha hb hunit) j t =
      markerReferenceNonthresholdOutput S a b ha hb hunit j t +
        (if j = 0 then VectorMeasure.dirac (0 : ℝ) (6 : ℝ) else 0) := by
  rw [correctedThermalFiniteOutputMeasure_eq,
    markerReferenceInput_threshold S a b ha hb hunit h0]
  rfl

/-- At the ordinary measure level the correction has exactly its marker and threshold atoms. -/
theorem markerReferenceThermalOutput_singleton (h0 : 0 ∈ S)
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalFiniteOutputMeasure S (markerReferenceInput S a b ha hb hunit) j t {e} =
      (if j = 0 ∧ e = b then Real.exp (-t * e) else 0) +
        (if j = 0 ∧ e = 0 then 6 else 0) := by
  rw [correctedThermalFiniteOutputMeasure_singleton S _ j (3 * b)
    (markerReferenceInput_physicalSupport S a b ha hb hunit) ht e,
    markerReferenceInput_singleton S a b ha hb hunit j e,
    markerReferenceInput_threshold S a b ha hb hunit h0,
    markerInput_singleton]
  by_cases hj : j = 0 <;> by_cases he : e = b <;> simp [hj, he, h0]

/-- Removing the canceled scalar threshold leaves exactly the prescribed unit marker. -/
theorem markerReferenceNonthresholdOutput_singleton (h0 : 0 ∈ S)
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    markerReferenceNonthresholdOutput S a b ha hb hunit j t {e} =
      if j = 0 ∧ e = b then Real.exp (-t * e) else 0 := by
  apply add_right_cancel (b := if j = 0 ∧ e = 0 then (6 : ℝ) else 0)
  calc
    _ = correctedThermalFiniteOutputMeasure S (markerReferenceInput S a b ha hb hunit)
        j t {e} := by
      rw [markerReferenceThermalOutput_eq S a b ha hb hunit h0]
      by_cases hj : j = 0 <;> by_cases he : e = 0 <;>
        simp [hj, he, VectorMeasure.dirac, eq_comm]
    _ = _ := markerReferenceThermalOutput_singleton S a b ha hb hunit h0 j ht e

/-- Every negative-energy vacuum measure is unchanged by the actual signed correction. -/
theorem markerReferenceThermalOutput_preserves_vacuum (V : SignedMeasure ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (V + correctedThermalFiniteOutputMeasure S (markerReferenceInput S a b ha hb hunit)
      j t).restrict (Iio (0 : ℝ)) = V.restrict (Iio (0 : ℝ)) :=
  add_correctedThermalFiniteOutputMeasure_restrict_negative V S _ j (3 * b)
    (markerReferenceInput_physicalSupport S a b ha hb hunit) ht

/-- The literal thermal coefficient of the vacuum continuum and the ordinary
marker reference output after cancellation of the scalar threshold. -/
def markerReferenceOutputCoefficient (y : ℝ) (j : ℤ) : ℂ :=
  (Real.sqrt y : ℂ) * (∫ e : ℝ,
    Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
      vacuumFullKernel a e j ∂referenceMeasure j) +
    (Real.sqrt y : ℂ) *
      (markerReferenceNonthresholdOutput S a b ha hb hunit j (2 * Real.pi * y) univ : ℂ)

/-- The complete ordinary spectral output reconstructs the actual modular
reference seed, with no remaining scalar threshold term. -/
theorem hasSum_markerReferenceSeed_output (h0 : 0 ∈ S)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => markerReferenceOutputCoefficient S a b ha hb hunit y j *
      cuspFourierMode j x)
      (markerReferenceSeed S a b ha hb hunit (rowPoint y hy x) - vacuumDirectRow a y x) := by
  have hout (j : ℤ) :
      correctedThermalFiniteOutputMeasure S (markerReferenceInput S a b ha hb hunit)
        j (2 * Real.pi * y) univ =
      markerReferenceNonthresholdOutput S a b ha hb hunit j (2 * Real.pi * y) univ +
        (if j = 0 then 6 else 0) := by
    rw [markerReferenceThermalOutput_eq S a b ha hb hunit h0]
    by_cases hj : j = 0 <;> simp [hj]
  have h := ((hasSum_vacuumFullKernel_fourier_laplace a y hy x).add
    (hasSum_correctedSeedSuperposition_thermalOutputMeasure S _ (3 * b)
      (markerReferenceInput_physicalSupport S a b ha hb hunit) y hy x)).sub
        (hasSum_ite_eq (0 : ℤ) (6 * (Real.sqrt y : ℂ)))
  unfold markerReferenceOutputCoefficient
  convert h using 1
  · funext j
    rw [hout j]
    by_cases hj : j = 0 <;> simp [hj] <;> ring
  · unfold markerReferenceSeed
    ring

/-- The reconstructed Fourier series is absolutely convergent at every height. -/
theorem summable_norm_markerReferenceSeed_output (h0 : 0 ∈ S)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    Summable (fun j : ℤ => ‖markerReferenceOutputCoefficient S a b ha hb hunit y j *
      cuspFourierMode j x‖) :=
  (hasSum_markerReferenceSeed_output S a b ha hb hunit h0 y hy x).summable.norm

/-- The complete reference function consists of its prescribed direct vacuum
and its convergent actual ordinary output, with the scalar atom canceled. -/
theorem markerReferenceSeed_eq_full_output (h0 : 0 ∈ S)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    markerReferenceSeed S a b ha hb hunit (rowPoint y hy x) = vacuumDirectRow a y x +
      ∑' j : ℤ, markerReferenceOutputCoefficient S a b ha hb hunit y j * cuspFourierMode j x := by
  rw [(hasSum_markerReferenceSeed_output S a b ha hb hunit h0 y hy x).tsum_eq]
  ring

/-- At the physical central-charge shift, the direct term is exactly the
specified vacuum character numerator. -/
theorem markerReferenceSeed_eq_character_output (c : ℝ) (hc : 2 ≤ GapFamily.shift c)
    (h0 : 0 ∈ S)
    (τ : UpperHalfPlane) :
    markerReferenceSeed S (GapFamily.shift c) b hc hb hunit τ =
      (Real.sqrt τ.im : ℂ) * GapFamily.vacuumNumerator c τ +
        ∑' j : ℤ, markerReferenceOutputCoefficient S (GapFamily.shift c) b hc hb hunit τ.im j *
          cuspFourierMode j τ.re := by
  have hrow : rowPoint τ.im τ.im_pos τ.re = τ := by
    apply UpperHalfPlane.ext
    exact Complex.eta _
  simpa only [hrow, vacuumDirectRow_eq_vacuumNumerator] using
    markerReferenceSeed_eq_full_output S (GapFamily.shift c) b hc hb hunit h0
      τ.im τ.im_pos τ.re

end GapFamily.Construction
