import GapFamily.Analytic.Poincare.Fourier.PoincareLowBandThermalOutput
import GapFamily.Analytic.Poincare.Repair.PoincareLocalInverseInput

/-! On a measurable region excluding zero, the actual thermal output is the
tilted direct input plus the actual ordinary corrected response density.
In particular this applies to the exterior above a nonnegative band cutoff.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set
open scoped Classical BigOperators

/-- Restriction away from zero removes the separately tracked scalar threshold
atom from the actual one-row thermal output. -/
theorem correctedThermalRowOutputMeasure_restrict_of_notMem_zero
    (ν : SignedMeasure ℝ) (J j : ℤ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    {t : ℝ} (ht : 0 < t) (A : Set ℝ) (hA : MeasurableSet A) (h0 : (0 : ℝ) ∉ A) :
    (correctedThermalRowOutputMeasure ν J j t).restrict A =
      (if j = J then thermalSignedInputMeasure (ν.restrict A) t else 0) +
        ((referenceMeasure j).restrict A).withDensityᵥ
          (correctedThermalRowDensity ν J j t) := by
  have hc : (correctedThermalContinuumMeasure ν J j t).restrict A =
      ((referenceMeasure j).restrict A).withDensityᵥ
        (correctedThermalRowDensity ν J j t) := by
    ext s hset
    rw [VectorMeasure.restrict_apply _ hA hset,
      correctedThermalContinuumMeasure_apply ν J j M hs ht _ (hset.inter hA),
      withDensityᵥ_apply (integrable_correctedThermalRowDensity ν J j M hs ht).restrict hset,
      Measure.restrict_restrict hset]
  simp only [correctedThermalRowOutputMeasure, VectorMeasure.restrict_add]
  rw [hc]
  have hd : (thermalSignedInputMeasure ν t).restrict A =
      thermalSignedInputMeasure (ν.restrict A) t :=
    VectorMeasure.restrict_withDensity (signedIntegrable_thermalInput ν J M hs ht)
  have ha : (if j = 0 then VectorMeasure.dirac (0 : ℝ)
      ((PoincareScalarFourier.scalarThresholdCoefficient J).re * ν univ) else 0).restrict A = 0 := by
    split_ifs <;> simp only [VectorMeasure.restrict_dirac_of_notMem h0,
      VectorMeasure.restrict_zero]
  rw [ha, add_zero]
  split_ifs <;> simp only [hd, VectorMeasure.restrict_zero]

/-- On every measurable set excluding zero, the finite actual thermal output
has exactly its restricted direct input and its ordinary corrected density. -/
theorem correctedThermalFiniteOutputMeasure_restrict_of_notMem_zero
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (M : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    {t : ℝ} (ht : 0 < t) (A : Set ℝ) (hA : MeasurableSet A) (h0 : (0 : ℝ) ∉ A) :
    (correctedThermalFiniteOutputMeasure S ν j t).restrict A =
      (if j ∈ S then thermalSignedInputMeasure ((ν j).restrict A) t else 0) +
        ((referenceMeasure j).restrict A).withDensityᵥ
          (fun e => Real.exp (-t * e) *
            (correctedSignedResponse (fun J : S => ν J) Subtype.val j e).re) := by
  have hr : (correctedThermalFiniteOutputMeasure S ν j t).restrict A =
      ∑ J ∈ S, (correctedThermalRowOutputMeasure (ν J) J j t).restrict A := by
    exact map_sum (VectorMeasure.restrictGm A) _ S
  rw [hr]
  rw [Finset.sum_congr rfl (fun J hJ =>
    correctedThermalRowOutputMeasure_restrict_of_notMem_zero (ν J) J j M (hs J hJ) ht A hA h0)]
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

/-- The exterior of any nonnegative band has the exact direct-plus-continuum
thermal output, with no threshold atom. -/
theorem correctedThermalFiniteOutputMeasure_restrict_Ioi
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (M : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    {t : ℝ} (ht : 0 < t) (B : ℝ) (hB : 0 ≤ B) :
    (correctedThermalFiniteOutputMeasure S ν j t).restrict (Ioi B) =
      (if j ∈ S then thermalSignedInputMeasure ((ν j).restrict (Ioi B)) t else 0) +
        ((referenceMeasure j).restrict (Ioi B)).withDensityᵥ
          (fun e => Real.exp (-t * e) *
            (correctedSignedResponse (fun J : S => ν J) Subtype.val j e).re) :=
  correctedThermalFiniteOutputMeasure_restrict_of_notMem_zero S ν j M hs ht
    (Ioi B) measurableSet_Ioi (not_lt_of_ge hB)

/-- The literal local inverse input has zero measure above its native band.
The result holds on every integer spin, including unselected rows. -/
theorem localInverseInput_restrict_Ioi
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) :
    (localInverseInput S ν M B hM hB hs hunit j).restrict (Ioi B) = 0 := by
  by_cases hj : j ∈ S
  · have hempty : Ioi B ∩ Ioo |(j : ℝ)| B = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (Set.disjoint_left.mpr
        (fun _ hE hband => (not_lt_of_gt hE) hband.2))
    calc
      _ = ((localInverseInput S ν M B hM hB hs hunit j).restrict
          (Ioo |(j : ℝ)| B)).restrict (Ioi B) := by
        rw [localInverseInput_restrict_self S ν M B hM hB hs hunit j hj]
      _ = (localInverseInput S ν M B hM hB hs hunit j).restrict
          (Ioi B ∩ Ioo |(j : ℝ)| B) :=
        VectorMeasure.restrict_restrict _ measurableSet_Ioi measurableSet_Ioo
      _ = 0 := by rw [hempty, VectorMeasure.restrict_empty]
  · simp [localInverseInput, hj]

end GapFamily.Analytic
