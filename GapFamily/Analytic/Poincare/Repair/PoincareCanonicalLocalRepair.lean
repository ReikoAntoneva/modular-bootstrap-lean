import GapFamily.Analytic.Poincare.Repair.PoincareActualLocalRepair
import GapFamily.Analytic.Poincare.Repair.PoincareLocalAnchorNormalization
import GapFamily.Analytic.Kernel.FullKernelInverse

/-! Canonical exact local repair. The spin set is the actual finite physical
low band, the inverse is supplied by the proved kernel positivity and coercivity,
and the actual scalar anchor has proved threshold mass one. No inverse or
anchor identity is a premise of these repair theorems.
-/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier
open scoped MatrixGroups

/-- Ordinary scalar-column integration normalizes the actual anchor. -/
theorem actualLocalAnchorInput_threshold_eq_one (S : Finset ℤ) (h0 : 0 ∈ S)
    (B : ℝ) (hB : 0 < B)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) :
    finiteSignedThresholdMass S (actualLocalAnchorInput S B hB hunit) = 1 :=
  finiteSignedThresholdMass_localAnchorInput_actual S h0 B hB hunit

/-- The canonical physical-band anchor uses the proved actual inverse. -/
def canonicalLocalAnchorInput (B : ℝ) (hB : 1 ≤ B) : ℤ → SignedMeasure ℝ :=
  actualLocalAnchorInput (lowBandSpinSet B) B (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical B hB)

theorem canonicalLocalAnchorInput_threshold (B : ℝ) (hB : 1 ≤ B) :
    finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalAnchorInput B hB) = 1 :=
  actualLocalAnchorInput_threshold_eq_one (lowBandSpinSet B)
    ((zero_mem_lowBandSpinSet B).mpr (by linarith)) B (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical B hB)

theorem canonicalLocalAnchorInput_physicalSupport (B : ℝ) (hB : 1 ≤ B) (j : ℤ) :
    ∀ᵐ E ∂(canonicalLocalAnchorInput B hB j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ 3 * B :=
  actualLocalAnchorInput_physicalSupport (lowBandSpinSet B) B (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical B hB) j

@[simp] theorem canonicalLocalAnchorInput_singleton (B : ℝ) (hB : 1 ≤ B)
    (j : ℤ) (e : ℝ) : canonicalLocalAnchorInput B hB j {e} = 0 :=
  actualLocalAnchorInput_singleton (lowBandSpinSet B) B (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical B hB) j e

theorem canonicalLocalAnchorInput_lowBandOutput (B : ℝ) (hB : 1 ≤ B)
    (j : ℤ) (hj : j ∈ lowBandSpinSet B) :
    finiteCorrectedLowBandOutput (lowBandSpinSet B) (canonicalLocalAnchorInput B hB)
      j (3 * B) B (fun J _ => canonicalLocalAnchorInput_physicalSupport B hB J) = 0 :=
  actualLocalAnchorInput_lowBandOutput (lowBandSpinSet B) B (by linarith)
    (isUnit_correctedLowBandIdentityPlus_canonical B hB) j hj

variable (ν : ℤ → SignedMeasure ℝ) (B : ℝ) (hB : 1 ≤ B)
  (hν : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * B)

/-- The actual local-repair input, with no chosen inverse or anchor assumption. -/
def canonicalLocalRepairInput : ℤ → SignedMeasure ℝ :=
  actualLocalRepairInput (lowBandSpinSet B) ν B (by linarith) hν
    (isUnit_correctedLowBandIdentityPlus_canonical B hB)

theorem canonicalLocalRepairInput_physicalSupport :
    ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(canonicalLocalRepairInput ν B hB hν J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * B :=
  actualLocalRepairInput_physicalSupport (lowBandSpinSet B) ν B (by linarith) hν
    (isUnit_correctedLowBandIdentityPlus_canonical B hB)

/-- Zeroth signed moments remove the threshold of the actual canonical repair. -/
theorem canonicalLocalRepairInput_threshold_eq_zero
    (hmoment : ∀ J ∈ lowBandSpinSet B, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0) :
    finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalRepairInput ν B hB hν) = 0 :=
  actualLocalRepairInput_threshold_eq_zero (lowBandSpinSet B) ν B (by linarith) hν
    (isUnit_correctedLowBandIdentityPlus_canonical B hB)
    (canonicalLocalAnchorInput_threshold B hB) hmoment

/-- The canonical repair is the literal actual corrected Poincaré superposition. -/
def canonicalLocalRepairSeed (τ : UpperHalfPlane) : ℂ :=
  correctedSeedSuperposition (lowBandSpinSet B) (canonicalLocalRepairInput ν B hB hν) τ

theorem canonicalLocalRepairSeed_smul (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    canonicalLocalRepairSeed ν B hB hν (g • τ) = canonicalLocalRepairSeed ν B hB hν τ :=
  correctedSeedSuperposition_smul (lowBandSpinSet B) _ τ g

/-- The full canonical repair output is its ordinary convergent Fourier–Laplace series. -/
theorem hasSum_canonicalLocalRepairSeed_output (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
        (canonicalLocalRepairInput ν B hB hν) j (2 * Real.pi * y) univ : ℂ) *
          cuspFourierMode j x)
      (canonicalLocalRepairSeed ν B hB hν (rowPoint y hy x)) :=
  hasSum_correctedSeedSuperposition_thermalOutputMeasure (lowBandSpinSet B) _ (3 * B)
    (canonicalLocalRepairInput_physicalSupport ν B hB hν) y hy x

/-- Exact local repair below the cutoff, for every output spin. The measure
contains the original input atoms, including physical-edge atoms. -/
theorem canonicalLocalRepairOutput_eq_input_below_cutoff
    (hmoment : ∀ J ∈ lowBandSpinSet B, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0)
    (hinside : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation, E < B)
    (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalRepairInput ν B hB hν) j t).restrict (Iio B) =
      if j ∈ lowBandSpinSet B then thermalSignedInputMeasure (ν j) t else 0 :=
  exactLocalRepairOutput_eq_finiteInput_below_cutoff (lowBandSpinSet B) ν B
    (by linarith) hν _ _ (isUnit_correctedLowBandIdentityPlus_canonical B hB)
    (canonicalLocalAnchorInput_threshold B hB) hmoment
    (fun j hj => (mem_lowBandSpinSet B j).mpr hj) hinside j ht

/-- All actual output atoms are original input atoms; the repair creates no
scalar-threshold atom and no atom at any other energy. -/
theorem canonicalLocalRepairOutput_singleton
    (hmoment : ∀ J ∈ lowBandSpinSet B, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0)
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalRepairInput ν B hB hν) j t {e} =
      if j ∈ lowBandSpinSet B then Real.exp (-t * e) * ν j {e} else 0 :=
  actualLocalRepairOutput_singleton (lowBandSpinSet B) ν B (by linarith) hν
    (isUnit_correctedLowBandIdentityPlus_canonical B hB)
    (canonicalLocalAnchorInput_threshold B hB) hmoment j ht e

/-- The complete negative-energy vacuum measure remains unchanged. -/
theorem canonicalLocalRepairOutput_preserves_vacuum (V : SignedMeasure ℝ) (j : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (V + correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalLocalRepairInput ν B hB hν) j t).restrict (Iio (0 : ℝ)) =
      V.restrict (Iio (0 : ℝ)) :=
  add_correctedThermalFiniteOutputMeasure_restrict_negative V (lowBandSpinSet B) _ j (3 * B)
    (canonicalLocalRepairInput_physicalSupport ν B hB hν) ht

end GapFamily.Analytic
