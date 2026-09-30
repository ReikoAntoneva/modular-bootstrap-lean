import GapFamily.Analytic.Poincare.Repair.PoincareLocalRepairOutput
import GapFamily.Analytic.Poincare.Repair.PoincareLocalAnchorCancellation
import GapFamily.Analytic.Poincare.Fourier.PoincareLowBandThermalOutput
import GapFamily.Analytic.Poincare.Fourier.PoincarePhysicalOutputSupport
import GapFamily.Analytic.Foundation.SignedBandRestriction

/-! Exact local repair built from the actual low-band inverse and the actual
ordinary scalar high-band anchor. Invertibility and the anchor's scalar
normalization are explicit premises; no cancellation or density existence
property is assumed of an abstract repair object.
-/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier
open scoped MatrixGroups

variable (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ) (hB : 0 < B)
  (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * B)
  (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B))
  (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))

/-- The repair's input uses the actual inverse measure and actual signed anchor. -/
def exactLocalRepairInput : ℤ → SignedMeasure ℝ :=
  localRepairInput S ν
    (localInverseInput S ν (3 * B) B (by positivity) hB.le hν hunit)
    (localAnchorInput S B hB ζ hζ hunit)

/-- Every seed used by the actual repair is physical and lies below `3B`. -/
theorem exactLocalRepairInput_physicalSupport :
    ∀ J ∈ S, ∀ᵐ E ∂(exactLocalRepairInput S ν B hB hν ζ hζ hunit J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * B :=
  localRepairInput_physicalSupport S ν _ _ (3 * B) hν
    (fun J _ => localInverseInput_ae_physical_le S ν (3 * B) B (by positivity) hB.le
      hν hunit (3 * B) (by linarith) J)
    (fun J _ => localAnchorInput_ae_physical S B hB ζ hζ hunit J)

/-- The actual inverse and signed high-band anchor preserve all original input atoms. -/
@[simp] theorem exactLocalRepairInput_singleton (j : ℤ) (e : ℝ) :
    exactLocalRepairInput S ν B hB hν ζ hζ hunit j {e} = ν j {e} :=
  localRepairInput_singleton S ν _ _ j e
    (localInverseInput_singleton S ν (3 * B) B (by positivity) hB.le hν hunit j e)
    (localAnchorInput_singleton S B hB ζ hζ hunit j e)

/-- The complete ordinary open low-band output is the original input there.
This follows from the actual inverse equation, not an assumed output identity. -/
theorem exactLocalRepairInput_lowBandOutput (j : ℤ) (hj : j ∈ S) :
    finiteCorrectedLowBandOutput S (exactLocalRepairInput S ν B hB hν ζ hζ hunit)
      j (3 * B) B (exactLocalRepairInput_physicalSupport S ν B hB hν ζ hζ hunit) =
      (ν j).restrict (Ioo |(j : ℝ)| B) := by
  let μ := localInverseInput S ν (3 * B) B (by positivity) hB.le hν hunit
  let θ := localAnchorInput S B hB ζ hζ hunit
  have hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * B :=
    fun J _ => localInverseInput_ae_physical_le S ν (3 * B) B (by positivity) hB.le
      hν hunit (3 * B) (by linarith) J
  have hθ : ∀ J ∈ S, ∀ᵐ E ∂(θ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * B :=
    fun J _ => localAnchorInput_ae_physical S B hB ζ hζ hunit J
  have hc : finiteCorrectedLowBandOutput S μ j (3 * B) B hμ =
      correctedSignedOutputMeasure (fun J : S => ν J) Subtype.val j (3 * B) B
        (fun J => hν J J.property) :=
    finiteCorrectedLowBandOutput_localInverseInput_of_le S ν (3 * B) B
      (by positivity) hB.le hν hunit (3 * B) (by linarith) j hj
  have ha : finiteCorrectedLowBandOutput S θ j (3 * B) B hθ = 0 :=
    finiteCorrectedLowBandOutput_localAnchorInput S B hB ζ hζ hunit j hj
  have h := localRepairInput_lowBandOutput_eq_direct S ν μ θ j (3 * B) B hν hμ hθ hc ha
  simpa only [ite_eq_left hj, μ, θ, exactLocalRepairInput] using h

/-- The actual Fourier output measure agrees with the original input on the
open low band, including its ordinary thermal weight. -/
theorem exactLocalRepairOutput_restrict_openLowBand (j : ℤ) (hj : j ∈ S)
    {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure S
      (exactLocalRepairInput S ν B hB hν ζ hζ hunit) j t).restrict (Ioo |(j : ℝ)| B) =
      (thermalSignedInputMeasure (ν j) t).restrict (Ioo |(j : ℝ)| B) := by
  rw [correctedThermalFiniteOutputMeasure_restrict_lowBand S _ j (3 * B) B
    (exactLocalRepairInput_physicalSupport S ν B hB hν ζ hζ hunit) ht,
    exactLocalRepairInput_lowBandOutput S ν B hB hν ζ hζ hunit j hj]
  exact (VectorMeasure.restrict_withDensity
    (signedIntegrable_thermalInput (ν j) j (3 * B) (hν j hj) ht)).symm

/-- The sole anchor normalization gives exact threshold cancellation for a
zeroth-moment-cancelling input. -/
theorem exactLocalRepairInput_threshold_eq_zero
    (hanchor : finiteSignedThresholdMass S (localAnchorInput S B hB ζ hζ hunit) = 1)
    (hmoment : ∀ J ∈ S, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0) :
    finiteSignedThresholdMass S (exactLocalRepairInput S ν B hB hν ζ hζ hunit) = 0 :=
  localRepairInput_threshold_eq_zero S ν _ _ hanchor hmoment

/-- The actual corrected finite Poincaré seed used for local repair. -/
def exactLocalRepairSeed (τ : UpperHalfPlane) : ℂ :=
  correctedSeedSuperposition S (exactLocalRepairInput S ν B hB hν ζ hζ hunit) τ

/-- The actual local repair is modular invariant. -/
theorem exactLocalRepairSeed_smul (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    exactLocalRepairSeed S ν B hB hν ζ hζ hunit (g • τ) =
      exactLocalRepairSeed S ν B hB hν ζ hζ hunit τ :=
  correctedSeedSuperposition_smul S _ τ g

/-- The actual repair has the complete ordinary signed output at every
horizontal point; convergence is supplied by the proved physical support. -/
theorem hasSum_exactLocalRepairSeed_output (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (correctedThermalFiniteOutputMeasure S (exactLocalRepairInput S ν B hB hν ζ hζ hunit)
        j (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x)
      (exactLocalRepairSeed S ν B hB hν ζ hζ hunit (rowPoint y hy x)) :=
  hasSum_correctedSeedSuperposition_thermalOutputMeasure S _ (3 * B)
    (exactLocalRepairInput_physicalSupport S ν B hB hν ζ hζ hunit) y hy x

/-- All actual output atoms of the repair are the original atoms. The anchor
and the ordinary inverse do not contribute any new atom, at zero or an edge. -/
theorem exactLocalRepairOutput_singleton
    (hanchor : finiteSignedThresholdMass S (localAnchorInput S B hB ζ hζ hunit) = 1)
    (hmoment : ∀ J ∈ S, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0)
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalFiniteOutputMeasure S (exactLocalRepairInput S ν B hB hν ζ hζ hunit)
      j t {e} = if j ∈ S then Real.exp (-t * e) * ν j {e} else 0 := by
  rw [correctedThermalFiniteOutputMeasure_singleton S _ j (3 * B)
    (exactLocalRepairInput_physicalSupport S ν B hB hν ζ hζ hunit) ht e,
    exactLocalRepairInput_threshold_eq_zero S ν B hB hν ζ hζ hunit hanchor hmoment,
    exactLocalRepairInput_singleton]
  simp

/-- The entire negative-energy vacuum measure is unchanged by actual repair. -/
theorem exactLocalRepairOutput_preserves_vacuum (V : SignedMeasure ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (V + correctedThermalFiniteOutputMeasure S
      (exactLocalRepairInput S ν B hB hν ζ hζ hunit) j t).restrict (Iio (0 : ℝ)) =
      V.restrict (Iio (0 : ℝ)) :=
  add_correctedThermalFiniteOutputMeasure_restrict_negative V S _ j (3 * B)
    (exactLocalRepairInput_physicalSupport S ν B hB hν ζ hζ hunit) ht

/-- The complete actual output below `B` is exactly the original signed input,
including any input atom at the physical edge. -/
theorem exactLocalRepairOutput_restrict_below_cutoff
    (hanchor : finiteSignedThresholdMass S (localAnchorInput S B hB ζ hζ hunit) = 1)
    (hmoment : ∀ J ∈ S, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0)
    (j : ℤ) (hj : j ∈ S) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure S
      (exactLocalRepairInput S ν B hB hν ζ hζ hunit) j t).restrict (Iio B) =
      (thermalSignedInputMeasure (ν j) t).restrict (Iio B) := by
  apply signedMeasure_restrict_Iio_eq_of_physical_band
    _ _ |(j : ℝ)| B
  · exact correctedThermalFiniteOutputMeasure_restrict_below_edge S _ j (3 * B)
      (exactLocalRepairInput_physicalSupport S ν B hB hν ζ hζ hunit) ht
  · ext s hs
    rw [VectorMeasure.restrict_apply _ measurableSet_Iio hs, _root_.zero_apply]
    exact thermalSignedInputMeasure_apply_eq_zero_below_edge (ν j) j (3 * B)
      (hν j hj) ht _ (hs.inter measurableSet_Iio) inter_subset_right
  · exact exactLocalRepairOutput_restrict_openLowBand S ν B hB hν ζ hζ hunit j hj ht
  · rw [exactLocalRepairOutput_singleton S ν B hB hν ζ hζ hunit hanchor hmoment j ht,
      ite_eq_left hj, thermalSignedInputMeasure_singleton (ν j) j (3 * B) (hν j hj) ht]

/-- For an input supported strictly below the cutoff, exact local repair
returns that entire original signed input as its complete low-energy output. -/
theorem exactLocalRepairOutput_eq_input_below_cutoff
    (hanchor : finiteSignedThresholdMass S (localAnchorInput S B hB ζ hζ hunit) = 1)
    (hmoment : ∀ J ∈ S, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0)
    (j : ℤ) (hj : j ∈ S) (hinside : ∀ᵐ E ∂(ν j).variation, E < B)
    {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure S
      (exactLocalRepairInput S ν B hB hν ζ hζ hunit) j t).restrict (Iio B) =
      thermalSignedInputMeasure (ν j) t := by
  rw [exactLocalRepairOutput_restrict_below_cutoff S ν B hB hν ζ hζ hunit
    hanchor hmoment j hj ht]
  have hrestrict := signedMeasure_restrict_eq_self_of_ae_mem (ν j) (Iio B)
    measurableSet_Iio hinside
  change ((ν j).withDensity (fun E => Real.exp (-t * E))
    (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip).restrict (Iio B) = _
  rw [VectorMeasure.restrict_withDensity
    (signedIntegrable_thermalInput (ν j) j (3 * B) (hν j hj) ht), hrestrict]
  rfl

/-- Covering every physical low spin upgrades the selected-row cancellation
to the entire low-energy output family. -/
theorem exactLocalRepairOutput_eq_finiteInput_below_cutoff
    (hanchor : finiteSignedThresholdMass S (localAnchorInput S B hB ζ hζ hunit) = 1)
    (hmoment : ∀ J ∈ S, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0)
    (hcover : ∀ j : ℤ, |(j : ℝ)| < B → j ∈ S)
    (hinside : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, E < B)
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure S
      (exactLocalRepairInput S ν B hB hν ζ hζ hunit) j t).restrict (Iio B) =
      if j ∈ S then thermalSignedInputMeasure (ν j) t else 0 := by
  by_cases hj : j ∈ S
  · rw [ite_eq_left hj]
    exact exactLocalRepairOutput_eq_input_below_cutoff S ν B hB hν ζ hζ hunit
      hanchor hmoment j hj (hinside j hj) ht
  · rw [ite_eq_right hj]
    have hBj : B ≤ |(j : ℝ)| := le_of_not_gt (fun h => hj (hcover j h))
    ext s hs
    rw [VectorMeasure.restrict_apply _ measurableSet_Iio hs, _root_.zero_apply]
    exact correctedThermalFiniteOutputMeasure_apply_eq_zero_below_edge S _ j (3 * B)
      (exactLocalRepairInput_physicalSupport S ν B hB hν ζ hζ hunit) ht _
      (hs.inter measurableSet_Iio) (inter_subset_right.trans (Iio_subset_Iio hBj))

end GapFamily.Analytic
