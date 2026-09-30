import GapFamily.Analytic.Kernel.FullKernelInverseCancellation
import GapFamily.Analytic.Foundation.ThresholdAnchorBandBound
import GapFamily.Analytic.Foundation.SignedPhysicalSupport

/-!
# Actual local inverse and anchor input

The inverse is the ordinary signed measure produced by the full low-band
operator, extended by zero away from the finite spin set. The anchor is the
literal high scalar band input minus the inverse response to that same input.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

/-- The native full inverse response, indexed by integer spin and zero outside
its finite set of rows. -/
def localInverseInput (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) : SignedMeasure ℝ :=
  if h : j ∈ S then
    correctedSignedInverseMeasure (fun J : S => ν J) (fun J : S => (J : ℤ))
      (fun k : S => (k : ℤ)) M B hM hB (fun J => hs J J.property) hunit ⟨j, h⟩
  else 0

/-- A selected integer row is precisely the native inverse signed measure. -/
theorem localInverseInput_apply (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) (hj : j ∈ S) :
    localInverseInput S ν M B hM hB hs hunit j =
      correctedSignedInverseMeasure (fun J : S => ν J) (fun J : S => (J : ℤ))
        (fun k : S => (k : ℤ)) M B hM hB (fun J => hs J J.property) hunit ⟨j, hj⟩ := by
  simp only [localInverseInput, dite_eq_left hj]

/-- The finite inverse input vanishes on every unselected spin row. -/
theorem localInverseInput_eq_zero_of_notMem (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) (hj : j ∉ S) : localInverseInput S ν M B hM hB hs hunit j = 0 := by
  simp only [localInverseInput, dite_eq_right hj]

/-- Restriction to the native open low band leaves a selected inverse row unchanged. -/
theorem localInverseInput_restrict_self (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) (hj : j ∈ S) :
    (localInverseInput S ν M B hM hB hs hunit j).restrict (Ioo |(j : ℝ)| B) =
      localInverseInput S ν M B hM hB hs hunit j := by
  rw [localInverseInput_apply S ν M B hM hB hs hunit j hj]
  exact correctedSignedInverseMeasure_restrict_self (fun J : S => ν J)
    (fun J : S => (J : ℤ)) (fun k : S => (k : ℤ)) M B hM hB
    (fun J => hs J J.property) hunit ⟨j, hj⟩

/-- The actual inverse input creates no atom at any energy. -/
@[simp] theorem localInverseInput_singleton (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) (E : ℝ) : localInverseInput S ν M B hM hB hs hunit j {E} = 0 := by
  by_cases hj : j ∈ S
  · rw [localInverseInput_apply S ν M B hM hB hs hunit j hj]
    exact correctedSignedInverseMeasure_singleton (fun J : S => ν J)
      (fun J : S => (J : ℤ)) (fun k : S => (k : ℤ)) M B hM hB
      (fun J => hs J J.property) hunit ⟨j, hj⟩ E
  · simp [localInverseInput, hj]

/-- Variation of the actual finite inverse input has compact physical support
bounded by the inverse output cutoff. -/
theorem localInverseInput_ae_physical (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) :
    ∀ᵐ E ∂(localInverseInput S ν M B hM hB hs hunit j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ B := by
  by_cases hj : j ∈ S
  · rw [localInverseInput_apply S ν M B hM hB hs hunit j hj]
    exact correctedSignedInverseMeasure_ae_physical (fun J : S => ν J)
      (fun J : S => (J : ℤ)) (fun k : S => (k : ℤ)) M B hM hB
      (fun J => hs J J.property) hunit ⟨j, hj⟩
  · simp [localInverseInput, hj]

/-- The native inverse support can be promoted to any larger common input cutoff. -/
theorem localInverseInput_ae_physical_le (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (M' : ℝ) (hBM : B ≤ M') (j : ℤ) :
    ∀ᵐ E ∂(localInverseInput S ν M B hM hB hs hunit j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ M' :=
  (localInverseInput_ae_physical S ν M B hM hB hs hunit j).mono
    (fun _ hE => ⟨hE.1, hE.2.trans hBM⟩)

/-- The actual high-band input is the ordinary scalar anchor measure, with
zero measure in every nonzero spin. -/
def localAnchorHighInput (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B)) (j : ℤ) : SignedMeasure ℝ :=
  if j = 0 then scalarAnchorBandMeasure B hB ζ hζ else 0

/-- The high scalar anchor input is supported in the physical interval up to `3B`. -/
theorem localAnchorHighInput_ae_physical (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B)) (j : ℤ) :
    ∀ᵐ E ∂(localAnchorHighInput B hB ζ hζ j).variation, |(j : ℝ)| ≤ E ∧ E ≤ 3 * B := by
  by_cases hj : j = 0
  · subst j
    simpa only [localAnchorHighInput, ite_true, Int.cast_zero] using
      scalarAnchorBandMeasure_ae_physical B hB ζ hζ
  · simp [localAnchorHighInput, hj]

/-- Every actual high-band input row is carried by the scalar anchor band. -/
theorem localAnchorHighInput_ae_mem (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B)) (j : ℤ) :
    ∀ᵐ E ∂(localAnchorHighInput B hB ζ hζ j).variation, E ∈ scalarAnchorBand B := by
  by_cases hj : j = 0
  · subst j
    simpa only [localAnchorHighInput, ite_true] using scalarAnchorBandMeasure_ae_mem B hB ζ hζ
  · simp [localAnchorHighInput, hj]

/-- The high scalar band input has zero restriction to every open low band. -/
theorem localAnchorHighInput_restrict_lowBand (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B)) (j : ℤ) :
    (localAnchorHighInput B hB ζ hζ j).restrict (Ioo |(j : ℝ)| B) = 0 := by
  by_cases hj : j = 0
  · subst j
    simp only [localAnchorHighInput, ite_true, Int.cast_zero, abs_zero]
    ext s hs
    rw [VectorMeasure.restrict_apply _ measurableSet_Ioo hs]
    change scalarAnchorBandMeasure B hB ζ hζ (s ∩ Ioo 0 B) = 0
    apply scalarAnchorBandMeasure_eq_zero_of_disjoint B hB ζ hζ _ (hs.inter measurableSet_Ioo)
    apply disjoint_left.mpr
    intro E hE hband
    have hb := hband.1
    change 2 * B ≤ E at hb
    linarith [hE.2.2]
  · simp [localAnchorHighInput, hj]

/-- The ordinary high-band anchor input has no singleton mass. -/
@[simp] theorem localAnchorHighInput_singleton (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B)) (j : ℤ) (E : ℝ) :
    localAnchorHighInput B hB ζ hζ j {E} = 0 := by
  by_cases hj : j = 0 <;> simp [localAnchorHighInput, hj]

/-- The actual local anchor input subtracts the full inverse response from
the same ordinary high scalar-band measure. -/
def localAnchorInput (S : Finset ℤ) (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) :
    ℤ → SignedMeasure ℝ :=
  localAnchorHighInput B hB ζ hζ -
    localInverseInput S (localAnchorHighInput B hB ζ hζ) (3 * B) B (by positivity) hB.le
      (fun J _ => localAnchorHighInput_ae_physical B hB ζ hζ J) hunit

/-- The literal anchor difference has ordinary physical support bounded by `3B`. -/
theorem localAnchorInput_ae_physical (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) :
    ∀ᵐ E ∂(localAnchorInput S B hB ζ hζ hunit j).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ 3 * B := by
  apply signedPhysicalSupport_sub _ _ j (3 * B)
    (localAnchorHighInput_ae_physical B hB ζ hζ j)
  exact localInverseInput_ae_physical_le S (localAnchorHighInput B hB ζ hζ)
    (3 * B) B (by positivity) hB.le
    (fun J _ => localAnchorHighInput_ae_physical B hB ζ hζ J) hunit
    (3 * B) (by linarith) j

/-- Neither the high band nor the inverse creates an atom in the actual anchor. -/
@[simp] theorem localAnchorInput_singleton (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) (E : ℝ) : localAnchorInput S B hB ζ hζ hunit j {E} = 0 := by
  simp [localAnchorInput]

end GapFamily.Analytic
