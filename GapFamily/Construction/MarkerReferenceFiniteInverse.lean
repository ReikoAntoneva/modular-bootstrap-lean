import GapFamily.Construction.MarkerReferenceInverse
import GapFamily.Analytic.Poincare.Fourier.PoincareLowBandOutput

/-!
# The actual marker inverse as a finite integer-spin input

The ordinary inverse rows are extended by zero to all integer spins. Their
finite corrected low-band output remains the exact vacuum-plus-marker source.
-/

noncomputable section

open MeasureTheory Set

namespace GapFamily.Construction

open Analytic

/-- The actual marker inverse, extended by zero outside its finite set of spins. -/
def markerReferenceInverseInput (S : Finset ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))
    (j : ℤ) : SignedMeasure ℝ :=
  if hj : j ∈ S then markerReferenceInverseMeasure Subtype.val a b ha hb hunit ⟨j, hj⟩ else 0

/-- Every selected row is the native ordinary signed inverse measure. -/
theorem markerReferenceInverseInput_apply (S : Finset ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))
    (j : ℤ) (hj : j ∈ S) :
    markerReferenceInverseInput S a b ha hb hunit j =
      markerReferenceInverseMeasure Subtype.val a b ha hb hunit ⟨j, hj⟩ := by
  simp only [markerReferenceInverseInput, dite_eq_left hj]

theorem markerReferenceInverseInput_eq_zero_of_notMem (S : Finset ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))
    (j : ℤ) (hj : j ∉ S) : markerReferenceInverseInput S a b ha hb hunit j = 0 := by
  simp only [markerReferenceInverseInput, dite_eq_right hj]

/-- Zero extension preserves the absence of all point atoms. -/
@[simp] theorem markerReferenceInverseInput_singleton (S : Finset ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))
    (j : ℤ) (e : ℝ) : markerReferenceInverseInput S a b ha hb hunit j {e} = 0 := by
  by_cases hj : j ∈ S
  · rw [markerReferenceInverseInput_apply S a b ha hb hunit j hj]
    exact markerReferenceInverseMeasure_singleton Subtype.val a b ha hb hunit ⟨j, hj⟩ e
  · simp [markerReferenceInverseInput, hj]

/-- The literal variation of every integer row is supported in the physical band. -/
theorem markerReferenceInverseInput_ae_physical (S : Finset ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b)) (j : ℤ) :
    ∀ᵐ E ∂(markerReferenceInverseInput S a b ha hb hunit j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ b := by
  by_cases hj : j ∈ S
  · rw [markerReferenceInverseInput_apply S a b ha hb hunit j hj]
    exact markerReferenceInverseMeasure_ae_physical Subtype.val a b ha hb hunit ⟨j, hj⟩
  · simp [markerReferenceInverseInput, hj]

/-- The actual inverse support also satisfies every larger common input cutoff. -/
theorem markerReferenceInverseInput_ae_physical_le (S : Finset ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))
    (M : ℝ) (hbM : b ≤ M) (j : ℤ) :
    ∀ᵐ E ∂(markerReferenceInverseInput S a b ha hb hunit j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ M :=
  (markerReferenceInverseInput_ae_physical S a b ha hb hunit j).mono
    (fun _ hE => ⟨hE.1, hE.2.trans hbM⟩)

/-- Restriction to the original open low band preserves a selected actual inverse row. -/
theorem markerReferenceInverseInput_restrict_self (S : Finset ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))
    (j : ℤ) (hj : j ∈ S) :
    (markerReferenceInverseInput S a b ha hb hunit j).restrict (Ioo |(j : ℝ)| b) =
      markerReferenceInverseInput S a b ha hb hunit j := by
  rw [markerReferenceInverseInput_apply S a b ha hb hunit j hj]
  exact markerReferenceInverseMeasure_restrict_self Subtype.val a b ha hb hunit ⟨j, hj⟩

/-- The finite actual inverse input has precisely the negative vacuum-plus-marker source
as its corrected low-band output on every selected row. -/
theorem finiteCorrectedLowBandOutput_markerReferenceInverseInput
    (S : Finset ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))
    (j : ℤ) (hj : j ∈ S) :
    finiteCorrectedLowBandOutput S (markerReferenceInverseInput S a b ha hb hunit) j b b
      (fun J _ => markerReferenceInverseInput_ae_physical S a b ha hb hunit J) =
      markerReferenceSourceMeasure a b j := by
  have hfamily : (fun J : S => markerReferenceInverseInput S a b ha hb hunit J) =
      markerReferenceInverseMeasure Subtype.val a b ha hb hunit := by
    funext J
    exact markerReferenceInverseInput_apply S a b ha hb hunit J J.property
  unfold finiteCorrectedLowBandOutput
  rw [ite_eq_left hj, markerReferenceInverseInput_restrict_self S a b ha hb hunit j hj]
  simp only [correctedSignedOutputMeasure_eq_withDensity, hfamily]
  rw [markerReferenceInverseInput_apply S a b ha hb hunit j hj]
  simpa only [correctedSignedOutputMeasure_eq_withDensity] using
    markerReferenceInverseMeasure_add_output Subtype.val a b ha hb hunit ⟨j, hj⟩

/-- Changing the common input cutoff leaves the exact marker inverse cancellation unchanged. -/
theorem finiteCorrectedLowBandOutput_markerReferenceInverseInput_of_le
    (S : Finset ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))
    (M : ℝ) (hbM : b ≤ M) (j : ℤ) (hj : j ∈ S) :
    finiteCorrectedLowBandOutput S (markerReferenceInverseInput S a b ha hb hunit) j M b
      (fun J _ => markerReferenceInverseInput_ae_physical_le S a b ha hb hunit M hbM J) =
      markerReferenceSourceMeasure a b j := by
  rw [finiteCorrectedLowBandOutput_inputCutoff_eq S _ j M b b _
    (fun J _ => markerReferenceInverseInput_ae_physical S a b ha hb hunit J)]
  exact finiteCorrectedLowBandOutput_markerReferenceInverseInput S a b ha hb hunit j hj

end GapFamily.Construction
