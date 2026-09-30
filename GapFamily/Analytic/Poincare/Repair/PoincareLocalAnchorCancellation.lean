import GapFamily.Analytic.Poincare.Repair.PoincareLocalInverseInput
import GapFamily.Analytic.Poincare.Fourier.PoincareLowBandOutput

/-! The actual inverse input cancels the actual induced low-band output. Applying
this to the ordinary high-band seed proves exact low-band vanishing of the actual
local anchor; no vanishing condition is assumed of an abstract anchor.
-/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory

/-- The integer-indexed actual inverse has the exact native signed-measure
output on every selected row. -/
theorem finiteCorrectedLowBandOutput_localInverseInput
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) (hj : j ∈ S) :
    finiteCorrectedLowBandOutput S (localInverseInput S ν M B hM hB hs hunit) j B B
      (fun J _ => localInverseInput_ae_physical S ν M B hM hB hs hunit J) =
      correctedSignedOutputMeasure (fun J : S => ν J) Subtype.val j M B
        (fun J => hs J J.property) := by
  have hfamily : (fun J : S => localInverseInput S ν M B hM hB hs hunit J) =
      correctedSignedInverseMeasure (fun J : S => ν J) Subtype.val Subtype.val M B hM hB
        (fun J => hs J J.property) hunit := by
    funext J
    exact localInverseInput_apply S ν M B hM hB hs hunit J J.property
  unfold finiteCorrectedLowBandOutput
  rw [ite_eq_left hj, localInverseInput_restrict_self S ν M B hM hB hs hunit j hj]
  simp only [correctedSignedOutputMeasure_eq_withDensity, hfamily]
  rw [localInverseInput_apply S ν M B hM hB hs hunit j hj]
  simpa only [correctedSignedOutputMeasure_eq_withDensity] using
    correctedSignedInverseMeasure_add_output (fun J : S => ν J) Subtype.val
      Subtype.val M B hM hB (fun J => hs J J.property) hunit ⟨j, hj⟩

/-- The same actual inverse cancellation is unchanged under a larger common
input cutoff, as needed for the repair's signed linear combination. -/
theorem finiteCorrectedLowBandOutput_localInverseInput_of_le
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (N : ℝ) (hBN : B ≤ N) (j : ℤ) (hj : j ∈ S) :
    finiteCorrectedLowBandOutput S (localInverseInput S ν M B hM hB hs hunit) j N B
      (fun J _ => localInverseInput_ae_physical_le S ν M B hM hB hs hunit N hBN J) =
      correctedSignedOutputMeasure (fun J : S => ν J) Subtype.val j M B
        (fun J => hs J J.property) := by
  rw [finiteCorrectedLowBandOutput_inputCutoff_eq S _ j N B B _
    (fun J _ => localInverseInput_ae_physical S ν M B hM hB hs hunit J)]
  exact finiteCorrectedLowBandOutput_localInverseInput S ν M B hM hB hs hunit j hj

/-- The high-band input contributes only its induced ordinary density to the
low-band output, since its literal direct measure is supported above the band. -/
theorem finiteCorrectedLowBandOutput_localAnchorHighInput
    (S : Finset ℤ) (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B)) (j : ℤ) :
    finiteCorrectedLowBandOutput S (localAnchorHighInput B hB ζ hζ) j (3 * B) B
      (fun J _ => localAnchorHighInput_ae_physical B hB ζ hζ J) =
      correctedSignedOutputMeasure (fun J : S => localAnchorHighInput B hB ζ hζ J)
        Subtype.val j (3 * B) B
        (fun J => localAnchorHighInput_ae_physical B hB ζ hζ J) := by
  unfold finiteCorrectedLowBandOutput
  rw [localAnchorHighInput_restrict_lowBand]
  split_ifs <;> simp only [zero_add]

/-- The actual high input minus its actual full inverse response has exactly
zero ordinary low-band output on each selected row. -/
theorem finiteCorrectedLowBandOutput_localAnchorInput
    (S : Finset ℤ) (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) (hj : j ∈ S) :
    finiteCorrectedLowBandOutput S (localAnchorInput S B hB ζ hζ hunit) j (3 * B) B
      (fun J _ => localAnchorInput_ae_physical S B hB ζ hζ hunit J) = 0 := by
  let ν := localAnchorHighInput B hB ζ hζ
  let hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * B :=
    fun J _ => localAnchorHighInput_ae_physical B hB ζ hζ J
  let μ := localInverseInput S ν (3 * B) B (by positivity) hB.le hs hunit
  have hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * B :=
    fun J _ => localInverseInput_ae_physical_le S ν (3 * B) B (by positivity) hB.le
      hs hunit (3 * B) (by linarith) J
  change finiteCorrectedLowBandOutput S (fun J => ν J - μ J) j (3 * B) B _ = 0
  rw [finiteCorrectedLowBandOutput_sub S ν μ j (3 * B) B hs hμ]
  rw [finiteCorrectedLowBandOutput_localInverseInput_of_le S ν (3 * B) B
    (by positivity) hB.le hs hunit (3 * B) (by linarith) j hj]
  rw [finiteCorrectedLowBandOutput_localAnchorHighInput]
  exact sub_self _

end GapFamily.Analytic
