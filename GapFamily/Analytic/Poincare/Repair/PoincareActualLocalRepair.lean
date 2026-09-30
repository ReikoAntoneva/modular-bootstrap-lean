import GapFamily.Analytic.Poincare.Repair.PoincareLocalRepair
import GapFamily.Analytic.Kernel.FullKernelScalarAnchorNonvanishing

/-! Local repair with the actual scalar inverse response in the anchor.
The high-band normalization is strictly positive by the proved nonvanishing
theorem. The scalar threshold-one identity remains explicit for the ordinary
column-integration argument to supply.
-/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier
open scoped MatrixGroups

/-- The actual scalar anchor uses the actual inverse threshold response. -/
def actualLocalAnchorInput (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) :
    ℤ → SignedMeasure ℝ :=
  localAnchorInput S B hB (scalarAnchorResponsePhysical (fun j : S => (j : ℤ)) B hB.le)
    (continuous_scalarAnchorResponsePhysical (fun j : S => (j : ℤ)) B hB.le).continuousOn hunit

/-- The denominator in the actual high-band anchor is strictly positive. -/
theorem actualLocalAnchorInput_normalization_pos (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) :
    0 < scalarAnchorSquareMass B
      (scalarAnchorResponsePhysical (fun j : S => (j : ℤ)) B hB.le) :=
  scalarAnchorSquareMass_actual_pos _ B hB hunit

theorem actualLocalAnchorInput_physicalSupport (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) :
    ∀ᵐ E ∂(actualLocalAnchorInput S B hB hunit j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ 3 * B :=
  localAnchorInput_ae_physical S B hB _ _ hunit j

@[simp] theorem actualLocalAnchorInput_singleton (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) (e : ℝ) :
    actualLocalAnchorInput S B hB hunit j {e} = 0 :=
  localAnchorInput_singleton S B hB _ _ hunit j e

/-- The actual normalized high-band density minus its actual inverse response
has zero low-band output, without a supplied cancellation hypothesis. -/
theorem actualLocalAnchorInput_lowBandOutput (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) (hj : j ∈ S) :
    finiteCorrectedLowBandOutput S (actualLocalAnchorInput S B hB hunit) j (3 * B) B
      (fun J _ => actualLocalAnchorInput_physicalSupport S B hB hunit J) = 0 :=
  finiteCorrectedLowBandOutput_localAnchorInput S B hB _ _ hunit j hj

variable (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ) (hB : 0 < B)
  (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * B)
  (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))

/-- The actual inverse and actual scalar anchor determine the repair input. -/
def actualLocalRepairInput : ℤ → SignedMeasure ℝ :=
  exactLocalRepairInput S ν B hB hν
    (scalarAnchorResponsePhysical (fun j : S => (j : ℤ)) B hB.le)
    (continuous_scalarAnchorResponsePhysical (fun j : S => (j : ℤ)) B hB.le).continuousOn hunit

theorem actualLocalRepairInput_physicalSupport :
    ∀ J ∈ S, ∀ᵐ E ∂(actualLocalRepairInput S ν B hB hν hunit J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * B :=
  exactLocalRepairInput_physicalSupport S ν B hB hν _ _ hunit

/-- The actual scalar threshold vanishes for the prescribed moment-cancelling input. -/
theorem actualLocalRepairInput_threshold_eq_zero
    (hanchor : finiteSignedThresholdMass S (actualLocalAnchorInput S B hB hunit) = 1)
    (hmoment : ∀ J ∈ S, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0) :
    finiteSignedThresholdMass S (actualLocalRepairInput S ν B hB hν hunit) = 0 :=
  exactLocalRepairInput_threshold_eq_zero S ν B hB hν _ _ hunit hanchor hmoment

/-- This is the literal corrected Poincaré superposition of the actual repair input. -/
def actualLocalRepairSeed (τ : UpperHalfPlane) : ℂ :=
  correctedSeedSuperposition S (actualLocalRepairInput S ν B hB hν hunit) τ

/-- The actual repair is modular invariant, without an output identification assumption. -/
theorem actualLocalRepairSeed_smul (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    actualLocalRepairSeed S ν B hB hν hunit (g • τ) =
      actualLocalRepairSeed S ν B hB hν hunit τ :=
  correctedSeedSuperposition_smul S _ τ g

/-- The actual repair has its complete, convergent ordinary signed spectral output. -/
theorem hasSum_actualLocalRepairSeed_output (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (correctedThermalFiniteOutputMeasure S (actualLocalRepairInput S ν B hB hν hunit)
        j (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x)
      (actualLocalRepairSeed S ν B hB hν hunit (rowPoint y hy x)) :=
  hasSum_correctedSeedSuperposition_thermalOutputMeasure S _ (3 * B)
    (actualLocalRepairInput_physicalSupport S ν B hB hν hunit) y hy x

/-- Below the repair cutoff the complete actual output is precisely the
original input, including all physical-edge atoms. -/
theorem actualLocalRepairOutput_restrict_below_cutoff
    (hanchor : finiteSignedThresholdMass S (actualLocalAnchorInput S B hB hunit) = 1)
    (hmoment : ∀ J ∈ S, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0)
    (j : ℤ) (hj : j ∈ S) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure S
      (actualLocalRepairInput S ν B hB hν hunit) j t).restrict (Iio B) =
      (thermalSignedInputMeasure (ν j) t).restrict (Iio B) :=
  exactLocalRepairOutput_restrict_below_cutoff S ν B hB hν _ _ hunit hanchor hmoment j hj ht

/-- The actual repair has exactly the original input atoms and no others. -/
theorem actualLocalRepairOutput_singleton
    (hanchor : finiteSignedThresholdMass S (actualLocalAnchorInput S B hB hunit) = 1)
    (hmoment : ∀ J ∈ S, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0)
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalFiniteOutputMeasure S (actualLocalRepairInput S ν B hB hν hunit)
      j t {e} = if j ∈ S then Real.exp (-t * e) * ν j {e} else 0 :=
  exactLocalRepairOutput_singleton S ν B hB hν _ _ hunit hanchor hmoment j ht e

/-- Every negative-energy vacuum measure is unchanged by adding the actual repair. -/
theorem actualLocalRepairOutput_preserves_vacuum (V : SignedMeasure ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (V + correctedThermalFiniteOutputMeasure S
      (actualLocalRepairInput S ν B hB hν hunit) j t).restrict (Iio (0 : ℝ)) =
      V.restrict (Iio (0 : ℝ)) :=
  exactLocalRepairOutput_preserves_vacuum S ν B hB hν _ _ hunit V j ht

end GapFamily.Analytic
