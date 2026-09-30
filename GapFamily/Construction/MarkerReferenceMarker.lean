import GapFamily.Analytic.Foundation.FiniteSeedThreshold
import GapFamily.Analytic.Poincare.Fourier.PoincareLowBandOutput

/-!
# The actual scalar marker input

The marker is one unit Dirac mass in spin zero at the cutoff energy. Its
ordinary corrected response is exactly the physical scalar kernel column.
Its direct measure lies outside the open low band, and its scalar threshold
mass is exactly minus one.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace GapFamily.Construction

open Analytic

/-- One unit scalar marker at energy `b`, with zero measure in every other spin. -/
def markerInput (b : ℝ) (j : ℤ) : SignedMeasure ℝ :=
  if j = 0 then VectorMeasure.dirac b (1 : ℝ) else 0

@[simp] theorem markerInput_zero (b : ℝ) :
    markerInput b 0 = VectorMeasure.dirac b (1 : ℝ) := by
  simp [markerInput]

@[simp] theorem markerInput_of_ne_zero (b : ℝ) {j : ℤ} (hj : j ≠ 0) :
    markerInput b j = 0 := by
  simp [markerInput, hj]

/-- Variation retains precisely the unit Dirac marker, without signed cancellation. -/
theorem markerInput_variation (b : ℝ) (j : ℤ) :
    (markerInput b j).variation = if j = 0 then Measure.dirac b else 0 := by
  by_cases hj : j = 0 <;> simp [markerInput, hj]

/-- The literal marker satisfies the physical variation-support requirement. -/
theorem markerInput_ae_physical (b : ℝ) (hb : 0 ≤ b) (j : ℤ) :
    ∀ᵐ E ∂(markerInput b j).variation, |(j : ℝ)| ≤ E ∧ E ≤ b := by
  rw [markerInput_variation]
  by_cases hj : j = 0
  · subst j
    simp [hb]
  · simp [hj]

/-- Its only atom is the scalar unit marker at the prescribed cutoff. -/
@[simp] theorem markerInput_singleton (b : ℝ) (j : ℤ) (e : ℝ) :
    markerInput b j {e} = if j = 0 ∧ e = b then 1 else 0 := by
  by_cases hj : j = 0 <;> by_cases he : e = b <;>
    simp [markerInput, VectorMeasure.dirac, hj, he]
  exact Ne.symm he

/-- The row's ordinary signed mass is exactly one in spin zero. -/
@[simp] theorem markerInput_mass (b : ℝ) (j : ℤ) :
    markerInput b j univ = if j = 0 then 1 else 0 := by
  by_cases hj : j = 0 <;> simp [markerInput, hj]

/-- The unit marker has unit ordinary total variation in the scalar row. -/
theorem markerInput_totalVariation (b : ℝ) (j : ℤ) :
    (markerInput b j).variation.real univ = if j = 0 then 1 else 0 := by
  rw [markerInput_variation]
  by_cases hj : j = 0 <;> simp [hj, Measure.real]

/-- The cutoff endpoint is outside every open low band. -/
@[simp] theorem markerInput_restrict_lowBand (b : ℝ) (j : ℤ) :
    (markerInput b j).restrict (Ioo |(j : ℝ)| b) = 0 := by
  by_cases hj : j = 0
  · subst j
    simp only [markerInput_zero, Int.cast_zero, abs_zero]
    exact VectorMeasure.restrict_dirac_of_notMem (by simp)
  · simp [markerInput, hj]

/-- The scalar marker contributes exactly minus one to the finite threshold coefficient. -/
@[simp] theorem finiteSignedThresholdMass_markerInput (S : Finset ℤ) (h0 : 0 ∈ S) (b : ℝ) :
    finiteSignedThresholdMass S (markerInput b) = -1 := by
  simp [finiteSignedThresholdMass, markerInput_mass, h0]

/-- One actual signed kernel integral evaluates at the scalar marker point. -/
theorem correctedSignedRowResponse_markerInput (b : ℝ) (J j : ℤ) (e : ℝ) :
    correctedSignedRowResponse (markerInput b J) J j e =
      if J = 0 then correctedKernel j 0 e b else 0 := by
  by_cases hJ : J = 0
  · subst J
    simp [markerInput, correctedSignedRowResponse]
  · simp [markerInput, correctedSignedRowResponse, hJ]

/-- Finite ordinary superposition preserves the exact physical scalar marker column. -/
theorem correctedSignedResponse_markerInput (S : Finset ℤ) (h0 : 0 ∈ S)
    (b : ℝ) (j : ℤ) (e : ℝ) :
    correctedSignedResponse (fun J : S => markerInput b J) Subtype.val j e =
      correctedKernel j 0 e b := by
  unfold correctedSignedResponse
  rw [Finset.sum_eq_single (⟨0, h0⟩ : S)]
  · rw [correctedSignedRowResponse_markerInput]
    simp
  · intro J _ hJ
    have hJ0 : (J : ℤ) ≠ 0 := fun h => hJ (Subtype.ext h)
    rw [correctedSignedRowResponse_markerInput, ite_eq_right hJ0]
  · simp

/-- The marker's actual low-band output is the ordinary scalar kernel density;
the direct marker atom is at the excluded cutoff endpoint. -/
theorem finiteCorrectedLowBandOutput_markerInput (S : Finset ℤ) (h0 : 0 ∈ S)
    (b : ℝ) (hb : 0 ≤ b) (j : ℤ) :
    finiteCorrectedLowBandOutput S (markerInput b) j b b
      (fun J _ => markerInput_ae_physical b hb J) =
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| b)).withDensityᵥ
        (fun e => (correctedKernel j 0 e b).re) := by
  simp only [finiteCorrectedLowBandOutput, markerInput_restrict_lowBand, ite_self, zero_add,
    correctedSignedOutputMeasure_eq_withDensity]
  congr 1
  funext e
  rw [correctedSignedResponse_markerInput S h0 b j e]

end GapFamily.Construction
