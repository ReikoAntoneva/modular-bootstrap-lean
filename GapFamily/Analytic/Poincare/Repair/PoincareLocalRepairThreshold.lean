import GapFamily.Analytic.Poincare.Repair.PoincareCanonicalLocalRepair

/-! The actual local repair preserves an arbitrary scalar threshold coefficient.
These identities retain the origin atom explicitly, so they apply to the fixed
gap endpoint as well as to inputs whose zeroth moments vanish.
-/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier

variable (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ) (hB : 0 < B)
  (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * B)
  (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B))
  (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))

/-- Normalization of the anchor preserves the original threshold coefficient,
without a moment-cancellation assumption. -/
theorem exactLocalRepairInput_threshold
    (hanchor : finiteSignedThresholdMass S (localAnchorInput S B hB ζ hζ hunit) = 1) :
    finiteSignedThresholdMass S (exactLocalRepairInput S ν B hB hν ζ hζ hunit) =
      finiteSignedThresholdMass S ν :=
  localRepairInput_threshold S ν _ _ hanchor

/-- The full output consists of the input atoms and its explicit scalar
threshold atom. The continuum and inverse correction introduce no other atom. -/
theorem exactLocalRepairOutput_singleton_with_threshold
    (hanchor : finiteSignedThresholdMass S (localAnchorInput S B hB ζ hζ hunit) = 1)
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalFiniteOutputMeasure S (exactLocalRepairInput S ν B hB hν ζ hζ hunit)
      j t {e} = (if j ∈ S then Real.exp (-t * e) * ν j {e} else 0) +
        (if j = 0 ∧ e = 0 then finiteSignedThresholdMass S ν else 0) := by
  rw [correctedThermalFiniteOutputMeasure_singleton S _ j (3 * B)
    (exactLocalRepairInput_physicalSupport S ν B hB hν ζ hζ hunit) ht e,
    exactLocalRepairInput_threshold S ν B hB hν ζ hζ hunit hanchor,
    exactLocalRepairInput_singleton]

/-- Below the cutoff, the ordinary input and its scalar threshold atom are
the entire repaired output, including physical-edge atoms. -/
theorem exactLocalRepairOutput_restrict_below_cutoff_with_threshold
    (hanchor : finiteSignedThresholdMass S (localAnchorInput S B hB ζ hζ hunit) = 1)
    (j : ℤ) (hj : j ∈ S) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure S
      (exactLocalRepairInput S ν B hB hν ζ hζ hunit) j t).restrict (Iio B) =
      (thermalSignedInputMeasure (ν j) t).restrict (Iio B) +
        (if j = 0 then VectorMeasure.dirac (0 : ℝ) (finiteSignedThresholdMass S ν)
          else 0) := by
  let θ : SignedMeasure ℝ :=
    if j = 0 then VectorMeasure.dirac (0 : ℝ) (finiteSignedThresholdMass S ν) else 0
  have hθbelow : θ.restrict (Iio |(j : ℝ)|) = 0 := by
    by_cases hzero : j = 0
    · simp [θ, hzero]
    · simp [θ, hzero]
  have hθband : θ.restrict (Ioo |(j : ℝ)| B) = 0 := by
    by_cases hzero : j = 0
    · simp [θ, hzero]
    · simp [θ, hzero]
  have hθcutoff : θ.restrict (Iio B) = θ := by
    by_cases hzero : j = 0
    · simp [θ, hzero, hB]
    · simp [θ, hzero]
  have hθatom : θ {|(j : ℝ)|} =
      if j = 0 ∧ |(j : ℝ)| = 0 then finiteSignedThresholdMass S ν else 0 := by
    by_cases hzero : j = 0 <;> simp [θ, hzero]
  have hrestr :
      (correctedThermalFiniteOutputMeasure S
        (exactLocalRepairInput S ν B hB hν ζ hζ hunit) j t).restrict (Iio B) =
        (thermalSignedInputMeasure (ν j) t + θ).restrict (Iio B) := by
    apply signedMeasure_restrict_Iio_eq_of_physical_band _ _ |(j : ℝ)| B
    · exact correctedThermalFiniteOutputMeasure_restrict_below_edge S _ j (3 * B)
        (exactLocalRepairInput_physicalSupport S ν B hB hν ζ hζ hunit) ht
    · rw [VectorMeasure.restrict_add, hθbelow, add_zero]
      ext s hs
      rw [VectorMeasure.restrict_apply _ measurableSet_Iio hs, _root_.zero_apply]
      exact thermalSignedInputMeasure_apply_eq_zero_below_edge (ν j) j (3 * B)
        (hν j hj) ht _ (hs.inter measurableSet_Iio) inter_subset_right
    · rw [VectorMeasure.restrict_add, hθband, add_zero]
      exact exactLocalRepairOutput_restrict_openLowBand S ν B hB hν ζ hζ hunit j hj ht
    · rw [exactLocalRepairOutput_singleton_with_threshold S ν B hB hν ζ hζ hunit
        hanchor j ht, ite_eq_left hj, _root_.add_apply, hθatom,
        thermalSignedInputMeasure_singleton (ν j) j (3 * B) (hν j hj) ht]
  simpa only [VectorMeasure.restrict_add, hθcutoff] using hrestr

/-- The actual inverse-response anchor preserves the original threshold mass. -/
theorem actualLocalRepairInput_threshold
    (hanchor : finiteSignedThresholdMass S (actualLocalAnchorInput S B hB hunit) = 1) :
    finiteSignedThresholdMass S (actualLocalRepairInput S ν B hB hν hunit) =
      finiteSignedThresholdMass S ν :=
  exactLocalRepairInput_threshold S ν B hB hν _ _ hunit hanchor

/-- Actual local repair retains the original input atoms and the explicit
scalar threshold atom, with no zeroth-moment premise. -/
theorem actualLocalRepairOutput_singleton_with_threshold
    (hanchor : finiteSignedThresholdMass S (actualLocalAnchorInput S B hB hunit) = 1)
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalFiniteOutputMeasure S (actualLocalRepairInput S ν B hB hν hunit)
      j t {e} = (if j ∈ S then Real.exp (-t * e) * ν j {e} else 0) +
        (if j = 0 ∧ e = 0 then finiteSignedThresholdMass S ν else 0) :=
  exactLocalRepairOutput_singleton_with_threshold S ν B hB hν _ _ hunit hanchor j ht e

/-- The entire actual low-energy output includes its scalar threshold atom. -/
theorem actualLocalRepairOutput_restrict_below_cutoff_with_threshold
    (hanchor : finiteSignedThresholdMass S (actualLocalAnchorInput S B hB hunit) = 1)
    (j : ℤ) (hj : j ∈ S) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure S
      (actualLocalRepairInput S ν B hB hν hunit) j t).restrict (Iio B) =
      (thermalSignedInputMeasure (ν j) t).restrict (Iio B) +
        (if j = 0 then VectorMeasure.dirac (0 : ℝ) (finiteSignedThresholdMass S ν)
          else 0) :=
  exactLocalRepairOutput_restrict_below_cutoff_with_threshold S ν B hB hν _ _ hunit
    hanchor j hj ht

section Canonical

variable (ν : ℤ → SignedMeasure ℝ) (B : ℝ) (hB : 1 ≤ B)
  (hν : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation,
    |(J : ℝ)| ≤ E ∧ E ≤ 3 * B)

/-- Canonical repair preserves arbitrary threshold mass with no extra premise. -/
theorem canonicalLocalRepairInput_threshold :
    finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalRepairInput ν B hB hν) =
      finiteSignedThresholdMass (lowBandSpinSet B) ν :=
  actualLocalRepairInput_threshold (lowBandSpinSet B) ν B (by linarith) hν
    (isUnit_correctedLowBandIdentityPlus_canonical B hB)
    (canonicalLocalAnchorInput_threshold B hB)

/-- All atoms of canonical repair, retaining the scalar threshold coefficient. -/
theorem canonicalLocalRepairOutput_singleton_with_threshold
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalRepairInput ν B hB hν) j t {e} =
      (if j ∈ lowBandSpinSet B then Real.exp (-t * e) * ν j {e} else 0) +
        (if j = 0 ∧ e = 0 then finiteSignedThresholdMass (lowBandSpinSet B) ν else 0) :=
  actualLocalRepairOutput_singleton_with_threshold (lowBandSpinSet B) ν B
    (by linarith) hν (isUnit_correctedLowBandIdentityPlus_canonical B hB)
    (canonicalLocalAnchorInput_threshold B hB) j ht e

/-- Every selected row agrees below the cutoff with the input plus its scalar
threshold atom. -/
theorem canonicalLocalRepairOutput_restrict_below_cutoff_with_threshold
    (j : ℤ) (hj : j ∈ lowBandSpinSet B) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalRepairInput ν B hB hν) j t).restrict (Iio B) =
      (thermalSignedInputMeasure (ν j) t +
        (if j = 0 then VectorMeasure.dirac (0 : ℝ)
          (finiteSignedThresholdMass (lowBandSpinSet B) ν) else 0)).restrict (Iio B) := by
  rw [VectorMeasure.restrict_add]
  have hthreshold :
      (if j = 0 then VectorMeasure.dirac (0 : ℝ)
          (finiteSignedThresholdMass (lowBandSpinSet B) ν) else 0).restrict (Iio B) =
        if j = 0 then VectorMeasure.dirac (0 : ℝ)
          (finiteSignedThresholdMass (lowBandSpinSet B) ν) else 0 := by
    by_cases hzero : j = 0 <;> simp [hzero, show 0 < B by linarith]
  rw [hthreshold]
  exact actualLocalRepairOutput_restrict_below_cutoff_with_threshold
    (lowBandSpinSet B) ν B (by linarith) hν
    (isUnit_correctedLowBandIdentityPlus_canonical B hB)
    (canonicalLocalAnchorInput_threshold B hB) j hj ht

/-- The physical cone supplies the same complete low-energy identity for all
output spins, including those outside the selected spin set. -/
theorem canonicalLocalRepairOutput_restrict_below_cutoff_all_with_threshold
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalRepairInput ν B hB hν) j t).restrict (Iio B) =
      ((if j ∈ lowBandSpinSet B then thermalSignedInputMeasure (ν j) t else 0) +
        (if j = 0 then VectorMeasure.dirac (0 : ℝ)
          (finiteSignedThresholdMass (lowBandSpinSet B) ν) else 0)).restrict (Iio B) := by
  by_cases hj : j ∈ lowBandSpinSet B
  · rw [ite_eq_left hj]
    exact canonicalLocalRepairOutput_restrict_below_cutoff_with_threshold ν B hB hν
      j hj ht
  · have hzero : j ≠ 0 := by
      intro h
      subst j
      exact hj ((zero_mem_lowBandSpinSet B).mpr (by linarith))
    have hBj : B ≤ |(j : ℝ)| := le_of_not_gt fun h => hj ((mem_lowBandSpinSet B j).mpr h)
    simp only [ite_eq_right hj, ite_eq_right hzero, add_zero, VectorMeasure.restrict_zero]
    ext s hs
    rw [VectorMeasure.restrict_apply _ measurableSet_Iio hs, _root_.zero_apply]
    exact correctedThermalFiniteOutputMeasure_apply_eq_zero_below_edge
      (lowBandSpinSet B) _ j (3 * B)
      (canonicalLocalRepairInput_physicalSupport ν B hB hν) ht _
      (hs.inter measurableSet_Iio) (inter_subset_right.trans (Iio_subset_Iio hBj))

/-- If the input is strictly below the repair cutoff, its whole thermal
measure and threshold atom are recovered in every low-energy output row. -/
theorem canonicalLocalRepairOutput_eq_input_below_cutoff_with_threshold
    (hinside : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation, E < B)
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalRepairInput ν B hB hν) j t).restrict (Iio B) =
      (if j ∈ lowBandSpinSet B then thermalSignedInputMeasure (ν j) t else 0) +
        (if j = 0 then VectorMeasure.dirac (0 : ℝ)
          (finiteSignedThresholdMass (lowBandSpinSet B) ν) else 0) := by
  rw [canonicalLocalRepairOutput_restrict_below_cutoff_all_with_threshold ν B hB hν
    j ht, VectorMeasure.restrict_add]
  congr 1
  · by_cases hj : j ∈ lowBandSpinSet B
    · rw [ite_eq_left hj]
      have hrestrict := signedMeasure_restrict_eq_self_of_ae_mem (ν j) (Iio B)
        measurableSet_Iio (hinside j hj)
      change ((ν j).withDensity (fun E => Real.exp (-t * E))
        (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip).restrict (Iio B) = _
      rw [VectorMeasure.restrict_withDensity
        (signedIntegrable_thermalInput (ν j) j (3 * B) (hν j hj) ht), hrestrict]
      rfl
    · simp [hj]
  · by_cases hzero : j = 0 <;> simp [hzero, show 0 < B by linarith]

/-- The same complete identity includes the cutoff endpoint: the only atom
there is the original direct input atom. -/
theorem canonicalLocalRepairOutput_restrict_closed_cutoff_with_threshold
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalRepairInput ν B hB hν) j t).restrict (Iic B) =
      ((if j ∈ lowBandSpinSet B then thermalSignedInputMeasure (ν j) t else 0) +
        (if j = 0 then VectorMeasure.dirac (0 : ℝ)
          (finiteSignedThresholdMass (lowBandSpinSet B) ν) else 0)).restrict (Iic B) := by
  have hBzero : B ≠ 0 := ne_of_gt (by linarith)
  have hatom :
      correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
        (canonicalLocalRepairInput ν B hB hν) j t {B} =
        ((if j ∈ lowBandSpinSet B then thermalSignedInputMeasure (ν j) t else 0) +
          (if j = 0 then VectorMeasure.dirac (0 : ℝ)
            (finiteSignedThresholdMass (lowBandSpinSet B) ν) else 0)) {B} := by
    rw [canonicalLocalRepairOutput_singleton_with_threshold ν B hB hν j ht]
    by_cases hj : j ∈ lowBandSpinSet B
    · simp only [ite_eq_left hj, _root_.add_apply]
      rw [thermalSignedInputMeasure_singleton (ν j) j (3 * B) (hν j hj) ht]
      by_cases hzero : j = 0 <;> simp [hzero, hBzero, Ne.symm hBzero]
    · have hzero : j ≠ 0 := by
        intro h
        subst j
        exact hj ((zero_mem_lowBandSpinSet B).mpr (by linarith))
      simp [hj, hzero, hBzero]
  rw [signedMeasure_restrict_Iic_eq, signedMeasure_restrict_Iic_eq,
    canonicalLocalRepairOutput_restrict_below_cutoff_all_with_threshold ν B hB hν j ht,
    hatom]

end Canonical

end GapFamily.Analytic
