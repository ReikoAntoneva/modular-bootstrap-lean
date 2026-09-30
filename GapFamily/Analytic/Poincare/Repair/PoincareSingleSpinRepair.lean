import GapFamily.Analytic.Poincare.Repair.PoincareExteriorReconstruction
import GapFamily.Analytic.Poincare.Repair.PoincareExteriorMoment

/-! A single actual signed input row embedded in the canonical finite repair.
The resulting low-energy output is the original tilted input, and its exterior
numerator is one ordinary signed integral of the actual repair kernel.
-/

noncomputable section
namespace GapFamily.Analytic

open MeasureTheory Set
open scoped Classical BigOperators MatrixGroups

/-- One genuine signed measure in one input spin, with zero input in every other row. -/
def singleSpinInput (jin : ℤ) (ν : SignedMeasure ℝ) (j : ℤ) : SignedMeasure ℝ :=
  if j = jin then ν else 0

@[simp] theorem singleSpinInput_self (jin : ℤ) (ν : SignedMeasure ℝ) :
    singleSpinInput jin ν jin = ν := by simp [singleSpinInput]

@[simp] theorem singleSpinInput_of_ne (jin : ℤ) (ν : SignedMeasure ℝ) {j : ℤ}
    (hj : j ≠ jin) : singleSpinInput jin ν j = 0 := by simp [singleSpinInput, hj]

/-- The literal row embedding preserves actual physical support. -/
theorem singleSpinInput_physicalSupport (jin : ℤ) (ν : SignedMeasure ℝ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) (j : ℤ) :
    ∀ᵐ E ∂(singleSpinInput jin ν j).variation, |(j : ℝ)| ≤ E ∧ E ≤ M := by
  by_cases hj : j = jin
  · subst j
    simpa only [singleSpinInput_self] using hν
  · simp [singleSpinInput, hj]

/-- Compact cell support supplies exactly the support premise of canonical repair. -/
theorem singleSpinInput_canonical_physicalSupport (jin : ℤ) (ν : SignedMeasure ℝ)
    (B : ℝ) (hB : 1 ≤ B) (L V : ℝ) (hL : |(jin : ℝ)| ≤ L) (hVB : V < B)
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V) :
    ∀ j ∈ lowBandSpinSet B, ∀ᵐ E ∂(singleSpinInput jin ν j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ 3 * B := by
  intro j _
  apply singleSpinInput_physicalSupport jin ν (3 * B) _ j
  exact hν.mono fun E hE => ⟨hL.trans hE.1, hE.2.trans (by linarith)⟩

theorem singleSpinInput_inside_cutoff (jin : ℤ) (ν : SignedMeasure ℝ) (B : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, E < B) (j : ℤ) :
    ∀ᵐ E ∂(singleSpinInput jin ν j).variation, E < B := by
  by_cases hj : j = jin
  · subst j
    simpa only [singleSpinInput_self] using hν
  · simp [singleSpinInput, hj]

theorem singleSpinInput_mem_lowBandSpinSet (jin : ℤ) (B L V : ℝ)
    (hL : |(jin : ℝ)| ≤ L) (hLV : L ≤ V) (hVB : V < B) :
    jin ∈ lowBandSpinSet B :=
  (mem_lowBandSpinSet B jin).mpr ((hL.trans hLV).trans_lt hVB)

/-- Zeroth square-root-coordinate cancellation is the actual ordinary zero moment. -/
theorem signedMoment_zero_of_sqrtCoordinate (jin : ℤ) (ν : SignedMeasure ℝ) {L V : ℝ}
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V) (k : ℕ)
    (hm : ∀ n ≤ k, (∫ᵛ x : ℝ, x ^ n ∂<•signedSqrtCoordinate jin ν) = 0) :
    (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•ν) = 0 := by
  have h := hm 0 (Nat.zero_le k)
  rw [signedSqrtCoordinate_moment jin ν hν 0] at h
  simpa only [pow_zero] using h

theorem singleSpinInput_moment_zero (jin : ℤ) (ν : SignedMeasure ℝ)
    (hzero : (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•ν) = 0) (j : ℤ) :
    (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•singleSpinInput jin ν j) = 0 := by
  by_cases hj : j = jin
  · subst j
    simpa only [singleSpinInput_self] using hzero
  · simp only [singleSpinInput_of_ne jin ν hj, VectorMeasure.integral_zero_vectorMeasure]

/-- The exterior numerator of one input row is exactly its one signed kernel integral. -/
theorem canonicalRepairExteriorNumerator_singleSpin (jin : ℤ) (ν : SignedMeasure ℝ)
    (B : ℝ) (hB : 1 ≤ B) (hjin : jin ∈ lowBandSpinSet B) (j : ℤ) (e : ℝ) :
    canonicalRepairExteriorNumerator (singleSpinInput jin ν) B hB j e =
      ∫ᵛ E, canonicalRepairKernelEnergy B hB j jin e E ∂<•ν := by
  unfold canonicalRepairExteriorNumerator
  rw [Finset.sum_eq_single (⟨jin, hjin⟩ : LowBandSpin B)]
  · simp only [singleSpinInput_self, canonicalRepairKernelEnergy, sqrtEnergyCoordinate]
  · intro J _ hJ
    have hne : (J : ℤ) ≠ jin := fun h => hJ (Subtype.ext h)
    simp only [singleSpinInput_of_ne jin ν hne, VectorMeasure.integral_zero_vectorMeasure]
  · simp

variable (jin : ℤ) (ν : SignedMeasure ℝ) (B : ℝ) (hB : 1 ≤ B)
  (hν : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ 3 * B)

/-- The actual canonical repair input associated to one physical signed row. -/
def canonicalSingleSpinRepairInput : ℤ → SignedMeasure ℝ :=
  canonicalLocalRepairInput (singleSpinInput jin ν) B hB
    (fun j _ => singleSpinInput_physicalSupport jin ν (3 * B) hν j)

/-- The actual modular Poincaré seed for the embedded physical signed row. -/
def canonicalSingleSpinRepairSeed (τ : UpperHalfPlane) : ℂ :=
  canonicalLocalRepairSeed (singleSpinInput jin ν) B hB
    (fun j _ => singleSpinInput_physicalSupport jin ν (3 * B) hν j) τ

theorem canonicalSingleSpinRepairSeed_smul (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    canonicalSingleSpinRepairSeed jin ν B hB hν (g • τ) =
      canonicalSingleSpinRepairSeed jin ν B hB hν τ :=
  canonicalLocalRepairSeed_smul (singleSpinInput jin ν) B hB _ τ g

theorem canonicalSingleSpinRepairInput_physicalSupport :
    ∀ j ∈ lowBandSpinSet B, ∀ᵐ E ∂(canonicalSingleSpinRepairInput jin ν B hB hν j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ 3 * B :=
  canonicalLocalRepairInput_physicalSupport (singleSpinInput jin ν) B hB _

theorem canonicalSingleSpinRepairInput_threshold_eq_zero
    (hzero : (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•ν) = 0) :
    finiteSignedThresholdMass (lowBandSpinSet B) (canonicalSingleSpinRepairInput jin ν B hB hν) = 0 :=
  canonicalLocalRepairInput_threshold_eq_zero (singleSpinInput jin ν) B hB _
    (fun j _ => singleSpinInput_moment_zero jin ν hzero j)

/-- Below the cutoff the complete repaired output is exactly the one original tilted row. -/
theorem canonicalSingleSpinRepairOutput_eq_input_below_cutoff
    (hjin : jin ∈ lowBandSpinSet B)
    (hzero : (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•ν) = 0)
    (hinside : ∀ᵐ E ∂ν.variation, E < B) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalSingleSpinRepairInput jin ν B hB hν) j t).restrict (Iio B) =
      if j = jin then thermalSignedInputMeasure ν t else 0 := by
  rw [canonicalSingleSpinRepairInput,
    canonicalLocalRepairOutput_eq_input_below_cutoff (singleSpinInput jin ν) B hB _
      (fun j _ => singleSpinInput_moment_zero jin ν hzero j)
      (fun j _ => singleSpinInput_inside_cutoff jin ν B hinside j) j ht]
  by_cases hj : j = jin
  · subst j
    simp only [hjin, ite_true, singleSpinInput_self]
  · simp only [singleSpinInput_of_ne jin ν hj, thermalSignedInputMeasure,
      VectorMeasure.withDensity_zero_vectorMeasure, ite_self, ite_eq_right hj]

/-- Every original atom is retained in its original spin, including the physical edge. -/
theorem canonicalSingleSpinRepairOutput_singleton
    (hjin : jin ∈ lowBandSpinSet B)
    (hzero : (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•ν) = 0)
    (j : ℤ) {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalFiniteOutputMeasure (lowBandSpinSet B)
      (canonicalSingleSpinRepairInput jin ν B hB hν) j t {e} =
      if j = jin then Real.exp (-t * e) * ν {e} else 0 := by
  rw [canonicalSingleSpinRepairInput,
    canonicalLocalRepairOutput_singleton (singleSpinInput jin ν) B hB _
      (fun j _ => singleSpinInput_moment_zero jin ν hzero j) j ht e]
  by_cases hj : j = jin
  · subst j
    simp only [hjin, ite_true, singleSpinInput_self]
  · simp only [singleSpinInput_of_ne jin ν hj, _root_.zero_apply,
      mul_zero, ite_self, ite_eq_right hj]

end GapFamily.Analytic
