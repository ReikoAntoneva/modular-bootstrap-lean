import GapFamily.Construction.MarkerReferenceKernelNumerator
import GapFamily.Construction.MarkerReferenceThermalMeasure
import GapFamily.Analytic.Foundation.SignedDensityPairing
import GapFamily.Analytic.Poincare.Repair.PoincareLocalAnchorVariation

/-!
# The ordinary density of the actual marker reference

All direct non-marker terms use the actual inverse representatives, extended
by zero from their physical bands. The full density adds the genuine vacuum
and signed kernel response to this ordinary integrable direct numerator.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace GapFamily.Construction

open Analytic

private theorem restricted_density_eq_indicator (μ : Measure ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) (f : ℝ → ℝ) (hf : Integrable f (μ.restrict s)) :
    (μ.restrict s).withDensityᵥ f = μ.withDensityᵥ (s.indicator f) := by
  ext t ht
  rw [withDensityᵥ_apply hf ht,
    withDensityᵥ_apply ((integrable_indicator_iff hs).mpr hf) ht,
    setIntegral_indicator hs, Measure.restrict_restrict ht]

private def inverseRowDensity {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (hB : 0 ≤ B) (hunit : IsUnit (correctedLowBandIdentityPlus J B))
    (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (i : ι) : ℝ → ℝ :=
  (Ioo |(J i : ℝ)| B).indicator (correctedLowBandInverseRealL1 J B hB hunit f hf i)

private theorem inverseRowDensity_integrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (hunit : IsUnit (correctedLowBandIdentityPlus J B))
    (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (i : ι) : Integrable (inverseRowDensity J B hB hunit f hf i) (referenceMeasure (J i)) :=
  (integrable_indicator_iff measurableSet_Ioo).mpr (L1.integrable_coeFn _)

private theorem inverseRowDensity_stronglyMeasurable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (hunit : IsUnit (correctedLowBandIdentityPlus J B))
    (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (i : ι) : StronglyMeasurable (inverseRowDensity J B hB hunit f hf i) :=
  (Lp.stronglyMeasurable _).indicator measurableSet_Ioo

private theorem inverseRowDensity_measure {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (hunit : IsUnit (correctedLowBandIdentityPlus J B))
    (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (i : ι) :
    (referenceMeasure (J i)).withDensityᵥ (inverseRowDensity J B hB hunit f hf i) =
      correctedLowBandInverseSignedMeasure J B hB hunit f hf i :=
  (restricted_density_eq_indicator _ _ measurableSet_Ioo _ (L1.integrable_coeFn _)).symm

private theorem inverseRowDensity_eq_zero {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (hunit : IsUnit (correctedLowBandIdentityPlus J B))
    (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (i : ι) {e : ℝ} (he : B ≤ e) : inverseRowDensity J B hB hunit f hf i e = 0 :=
  indicator_of_notMem (fun h => not_lt_of_ge he h.2) _

private def markerInverseDensity (S : Finset ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))
    (j : ℤ) : ℝ → ℝ :=
  if hj : j ∈ S then inverseRowDensity Subtype.val b hb hunit
    (markerReferenceRhsHilbert Subtype.val a b ha hb)
    (markerReferenceRhsHilbert_integrable Subtype.val a b ha hb) ⟨j, hj⟩ else 0

private theorem markerInverseDensity_integrable (S : Finset ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b)) (j : ℤ) :
    Integrable (markerInverseDensity S a b ha hb hunit j) (referenceMeasure j) := by
  unfold markerInverseDensity
  split_ifs with hj
  · exact inverseRowDensity_integrable _ _ _ _ _ _ _
  · exact integrable_zero _ _ _

private theorem markerInverseDensity_stronglyMeasurable (S : Finset ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b)) (j : ℤ) :
    StronglyMeasurable (markerInverseDensity S a b ha hb hunit j) := by
  unfold markerInverseDensity
  split_ifs
  · exact inverseRowDensity_stronglyMeasurable _ _ _ _ _ _ _
  · exact stronglyMeasurable_zero

private theorem markerInverseDensity_measure (S : Finset ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b)) (j : ℤ) :
    (referenceMeasure j).withDensityᵥ (markerInverseDensity S a b ha hb hunit j) =
      markerReferenceInverseInput S a b ha hb hunit j := by
  by_cases hj : j ∈ S
  · rw [markerInverseDensity, dite_eq_left hj, markerReferenceInverseInput_apply S a b ha hb hunit j hj]
    simpa only [markerReferenceInverseMeasure] using
      (inverseRowDensity_measure (fun J : S => (J : ℤ)) b hb hunit
        (markerReferenceRhsHilbert (fun J : S => (J : ℤ)) a b ha hb)
        (markerReferenceRhsHilbert_integrable (fun J : S => (J : ℤ)) a b ha hb) ⟨j, hj⟩)
  · simp [markerInverseDensity, markerReferenceInverseInput, hj]

private theorem markerInverseDensity_eq_zero (S : Finset ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b))
    (j : ℤ) {e : ℝ} (he : b ≤ e) : markerInverseDensity S a b ha hb hunit j e = 0 := by
  unfold markerInverseDensity
  split_ifs
  · exact inverseRowDensity_eq_zero _ _ _ _ _ _ _ he
  · rfl

private def localInverseDensity (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) : ℝ → ℝ :=
  if hj : j ∈ S then inverseRowDensity Subtype.val B hB hunit
    (correctedSignedResponseHilbert (fun J : S => ν J) Subtype.val Subtype.val M B hM hB
      (fun J => hs J J.property))
    (correctedSignedResponseHilbert_integrable (fun J : S => ν J) Subtype.val Subtype.val M B
      hM hB (fun J => hs J J.property)) ⟨j, hj⟩ else 0

private theorem localInverseDensity_integrable (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) :
    Integrable (localInverseDensity S ν M B hM hB hs hunit j) (referenceMeasure j) := by
  unfold localInverseDensity
  split_ifs
  · exact inverseRowDensity_integrable _ _ _ _ _ _ _
  · exact integrable_zero _ _ _

private theorem localInverseDensity_stronglyMeasurable (S : Finset ℤ)
    (ν : ℤ → SignedMeasure ℝ) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) :
    StronglyMeasurable (localInverseDensity S ν M B hM hB hs hunit j) := by
  unfold localInverseDensity
  split_ifs
  · exact inverseRowDensity_stronglyMeasurable _ _ _ _ _ _ _
  · exact stronglyMeasurable_zero

private theorem localInverseDensity_measure (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) :
    (referenceMeasure j).withDensityᵥ (localInverseDensity S ν M B hM hB hs hunit j) =
      localInverseInput S ν M B hM hB hs hunit j := by
  by_cases hj : j ∈ S
  · rw [localInverseDensity, dite_eq_left hj,
      localInverseInput_apply S ν M B hM hB hs hunit j hj]
    simpa only [correctedSignedInverseMeasure] using
      (inverseRowDensity_measure (fun J : S => (J : ℤ)) B hB hunit
        (correctedSignedResponseHilbert (fun J : S => ν J) Subtype.val Subtype.val M B hM hB
          (fun J => hs J J.property))
        (correctedSignedResponseHilbert_integrable (fun J : S => ν J) Subtype.val Subtype.val
          M B hM hB (fun J => hs J J.property)) ⟨j, hj⟩)
  · simp [localInverseDensity, localInverseInput, hj]

private theorem localInverseDensity_eq_zero (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) {e : ℝ} (he : B ≤ e) : localInverseDensity S ν M B hM hB hs hunit j e = 0 := by
  unfold localInverseDensity
  split_ifs
  · exact inverseRowDensity_eq_zero _ _ _ _ _ _ _ he
  · rfl

private def anchorHighDensity (B : ℝ) (ζ : ℝ → ℝ) (j : ℤ) : ℝ → ℝ :=
  if j = 0 then scalarAnchorNumerator B ζ else 0

private theorem anchorHighDensity_integrable (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : Continuous ζ) (j : ℤ) :
    Integrable (anchorHighDensity B ζ j) (referenceMeasure j) := by
  by_cases hj : j = 0
  · subst j
    exact scalarAnchorNumerator_integrable B hB ζ hζ.continuousOn
  · simp only [anchorHighDensity, ite_eq_right hj]
    exact integrable_zero _ _ _

private theorem anchorHighDensity_stronglyMeasurable (B : ℝ)
    (ζ : ℝ → ℝ) (hζ : Continuous ζ) (j : ℤ) :
    StronglyMeasurable (anchorHighDensity B ζ j) := by
  unfold anchorHighDensity
  split_ifs
  · exact (hζ.div_const (scalarAnchorSquareMass B ζ)).stronglyMeasurable.indicator measurableSet_Icc
  · exact stronglyMeasurable_zero

private theorem anchorHighDensity_measure (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : Continuous ζ) (j : ℤ) :
    (referenceMeasure j).withDensityᵥ (anchorHighDensity B ζ j) =
      localAnchorHighInput B hB ζ hζ.continuousOn j := by
  by_cases hj : j = 0
  · subst j
    exact (scalarAnchorBandMeasure_eq_referenceDensity B hB ζ hζ.continuousOn).symm
  · simp [anchorHighDensity, localAnchorHighInput, hj]

private def anchorDensity (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : Continuous ζ)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) : ℝ → ℝ :=
  anchorHighDensity B ζ j -
    localInverseDensity S (localAnchorHighInput B hB ζ hζ.continuousOn) (3 * B) B
      (by positivity) hB.le (fun J _ => localAnchorHighInput_ae_physical B hB ζ hζ.continuousOn J) hunit j

private theorem anchorDensity_integrable (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : Continuous ζ)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) :
    Integrable (anchorDensity S B hB ζ hζ hunit j) (referenceMeasure j) :=
  (anchorHighDensity_integrable B hB ζ hζ j).sub (localInverseDensity_integrable _ _ _ _ _ _ _ _ j)

private theorem anchorDensity_stronglyMeasurable (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : Continuous ζ)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) :
    StronglyMeasurable (anchorDensity S B hB ζ hζ hunit j) :=
  (anchorHighDensity_stronglyMeasurable B ζ hζ j).sub
    (localInverseDensity_stronglyMeasurable _ _ _ _ _ _ _ _ j)

private theorem anchorDensity_measure (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : Continuous ζ)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (j : ℤ) :
    (referenceMeasure j).withDensityᵥ (anchorDensity S B hB ζ hζ hunit j) =
      localAnchorInput S B hB ζ hζ.continuousOn hunit j := by
  rw [anchorDensity, withDensityᵥ_sub (anchorHighDensity_integrable B hB ζ hζ j)
    (localInverseDensity_integrable _ _ _ _ _ _ _ _ j),
    anchorHighDensity_measure B hB ζ hζ j, localInverseDensity_measure]
  rfl

private theorem anchorDensity_eq_zero (S : Finset ℤ) (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : Continuous ζ)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B))
    (j : ℤ) {e : ℝ} (he : 3 * B < e) : anchorDensity S B hB ζ hζ hunit j e = 0 := by
  have hlow := localInverseDensity_eq_zero S (localAnchorHighInput B hB ζ hζ.continuousOn)
    (3 * B) B (by positivity) hB.le
    (fun J _ => localAnchorHighInput_ae_physical B hB ζ hζ.continuousOn J) hunit j
    (show B ≤ e by linarith)
  have hhigh : anchorHighDensity B ζ j e = 0 := by
    unfold anchorHighDensity
    split_ifs
    · exact indicator_of_notMem (fun h => not_le_of_gt he h.2) _
    · rfl
  exact sub_eq_zero.mpr (hhigh.trans hlow.symm)

/-- The actual direct non-marker density, with explicit low-band and high-band indicators. -/
def canonicalMarkerReferenceDirectDensity (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) : ℝ → ℝ :=
  markerInverseDensity (lowBandSpinSet b) a b ha (zero_le_one.trans hb)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb) j +
  markerReferenceAnchorCoefficient (lowBandSpinSet b) a b ha (by linarith)
      (isUnit_correctedLowBandIdentityPlus_canonical b hb) •
    anchorDensity (lowBandSpinSet b) b (by linarith)
      (scalarAnchorResponsePhysical (fun J : lowBandSpinSet b => (J : ℤ)) b (zero_le_one.trans hb))
      (continuous_scalarAnchorResponsePhysical (fun J : lowBandSpinSet b => (J : ℤ)) b (zero_le_one.trans hb))
      (isUnit_correctedLowBandIdentityPlus_canonical b hb) j

theorem canonicalMarkerReferenceDirectDensity_integrable (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) :
    Integrable (canonicalMarkerReferenceDirectDensity a b ha hb j) (referenceMeasure j) :=
  (markerInverseDensity_integrable _ _ _ _ _ _ j).add
    ((anchorDensity_integrable _ _ _ _ _ _ j).smul _)

theorem canonicalMarkerReferenceDirectDensity_stronglyMeasurable (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) :
    StronglyMeasurable (canonicalMarkerReferenceDirectDensity a b ha hb j) :=
  (markerInverseDensity_stronglyMeasurable _ _ _ _ _ _ j).add
    ((anchorDensity_stronglyMeasurable _ _ _ _ _ _ j).const_smul _)

/-- The actual canonical input is exactly its unit marker plus its ordinary direct density. -/
theorem canonicalMarkerReferenceInput_eq_marker_add_density (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) :
    canonicalMarkerReferenceInput a b ha hb j = markerInput b j +
      (referenceMeasure j).withDensityᵥ (canonicalMarkerReferenceDirectDensity a b ha hb j) := by
  rw [canonicalMarkerReferenceDirectDensity,
    withDensityᵥ_add (markerInverseDensity_integrable _ _ _ _ _ _ j)
      ((anchorDensity_integrable _ _ _ _ _ _ j).smul _),
    withDensityᵥ_smul, markerInverseDensity_measure, anchorDensity_measure]
  simp only [canonicalMarkerReferenceInput, markerReferenceInput, actualLocalAnchorInput,
    Pi.add_apply, Pi.smul_apply]
  exact add_assoc _ _ _

/-- The actual direct density is pointwise zero beyond the compact input cutoff. -/
theorem canonicalMarkerReferenceDirectDensity_eq_zero (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {e : ℝ} (he : 3 * b < e) :
    canonicalMarkerReferenceDirectDensity a b ha hb j e = 0 := by
  have hm := markerInverseDensity_eq_zero (lowBandSpinSet b) a b ha (zero_le_one.trans hb)
    (isUnit_correctedLowBandIdentityPlus_canonical b hb) j (show b ≤ e by linarith)
  have ht := anchorDensity_eq_zero (lowBandSpinSet b) b (by linarith)
    (scalarAnchorResponsePhysical (fun J : lowBandSpinSet b => (J : ℤ)) b (zero_le_one.trans hb))
    (continuous_scalarAnchorResponsePhysical (fun J : lowBandSpinSet b => (J : ℤ)) b (zero_le_one.trans hb))
    (isUnit_correctedLowBandIdentityPlus_canonical b hb) j he
  simp only [canonicalMarkerReferenceDirectDensity, Pi.add_apply, Pi.smul_apply, hm, ht,
    smul_zero, add_zero]

/-- The complete ordinary density of the canonical reference, excluding its unit marker. -/
def canonicalMarkerReferenceDensity (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) (e : ℝ) : ℝ :=
  canonicalMarkerReferenceDirectDensity a b ha hb j e +
    canonicalMarkerReferenceKernelNumerator a b ha hb j e

/-- Beyond the compact direct input, the density is exactly the genuine vacuum-plus-response. -/
theorem canonicalMarkerReferenceDensity_eq_kernelNumerator (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) {e : ℝ} (he : 3 * b < e) :
    canonicalMarkerReferenceDensity a b ha hb j e =
      canonicalMarkerReferenceKernelNumerator a b ha hb j e := by
  rw [canonicalMarkerReferenceDensity, canonicalMarkerReferenceDirectDensity_eq_zero a b ha hb j he,
    zero_add]

/-- Every finite physical energy band has ordinary absolute density mass. -/
theorem canonicalMarkerReferenceDensity_integrable (a b W : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) :
    Integrable (canonicalMarkerReferenceDensity a b ha hb j)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| W)) :=
  (canonicalMarkerReferenceDirectDensity_integrable a b ha hb j).restrict.add
    (canonicalMarkerReferenceKernelNumerator_integrable a b W ha hb j)

/-- The literal density is globally strongly measurable, including the band edges. -/
theorem canonicalMarkerReferenceDensity_stronglyMeasurable (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) :
    StronglyMeasurable (canonicalMarkerReferenceDensity a b ha hb j) := by
  have hs : StronglyMeasurable (correctedSignedResponse
      (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
      Subtype.val j) := by
    unfold correctedSignedResponse
    exact (Finset.stronglyMeasurable_fun_sum Finset.univ (fun (J : lowBandSpinSet b) _ =>
        correctedSignedRowResponse_stronglyMeasurable _ _ j (3 * b)
          (canonicalMarkerReferenceInput_physicalSupport a b ha hb J)))
  exact (canonicalMarkerReferenceDirectDensity_stronglyMeasurable a b ha hb j).add
    ((Complex.continuous_re.comp (continuous_vacuumFullKernel a j)).stronglyMeasurable.add (Complex.continuous_re.comp_stronglyMeasurable hs))

/-- No direct ordinary input is introduced outside the selected spin set. -/
theorem canonicalMarkerReferenceDirectDensity_eq_zero_of_notMem (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) (hj : j ∉ lowBandSpinSet b) :
    canonicalMarkerReferenceDirectDensity a b ha hb j = 0 := by
  have hj0 : j ≠ 0 := by
    intro h
    subst j
    exact hj ((zero_mem_lowBandSpinSet b).mpr (zero_lt_one.trans_le hb))
  simp [canonicalMarkerReferenceDirectDensity, markerInverseDensity,
    anchorDensity, anchorHighDensity, localInverseDensity, hj, hj0]

/-- Ordinary direct mass is bounded by the actual input variation and its marker. -/
theorem integral_abs_canonicalMarkerReferenceDirectDensity_le_variation (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) :
    (∫ e, |canonicalMarkerReferenceDirectDensity a b ha hb j e| ∂referenceMeasure j) ≤
      (canonicalMarkerReferenceInput a b ha hb j).variation.real univ +
        if j = 0 then 1 else 0 := by
  have hμ : (referenceMeasure j).withDensityᵥ
      (canonicalMarkerReferenceDirectDensity a b ha hb j) =
      canonicalMarkerReferenceInput a b ha hb j - markerInput b j := by
    rw [canonicalMarkerReferenceInput_eq_marker_add_density]
    abel
  rw [← signedDensity_totalVariation
    (canonicalMarkerReferenceDirectDensity_integrable a b ha hb j), hμ]
  simpa only [markerInput_totalVariation] using
    signedMeasure_variation_real_sub_le (canonicalMarkerReferenceInput a b ha hb j) (markerInput b j)

/-- A uniform row version of the ordinary direct mass estimate. -/
theorem integral_abs_canonicalMarkerReferenceDirectDensity_le (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) :
    (∫ e, |canonicalMarkerReferenceDirectDensity a b ha hb j e| ∂referenceMeasure j) ≤
      (canonicalMarkerReferenceInput a b ha hb j).variation.real univ + 1 := by
  apply (integral_abs_canonicalMarkerReferenceDirectDensity_le_variation a b ha hb j).trans
  exact add_le_add le_rfl (by split_ifs <;> norm_num)

/-- Any finite collection of direct rows has at most the actual input mass plus one. -/
theorem sum_integral_abs_canonicalMarkerReferenceDirectDensity_le (S : Finset ℤ)
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    (∑ j ∈ S, ∫ e, |canonicalMarkerReferenceDirectDensity a b ha hb j e| ∂referenceMeasure j) ≤
      signedSeedMass (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) + 1 := by
  let m : ℤ → ℝ := fun j => ∫ e,
    |canonicalMarkerReferenceDirectDensity a b ha hb j e| ∂referenceMeasure j
  have hm (j : ℤ) : 0 ≤ m j := integral_nonneg (fun _ => abs_nonneg _)
  have hzero (j : ℤ) (hj : j ∉ lowBandSpinSet b) : m j = 0 := by
    simp [m, canonicalMarkerReferenceDirectDensity_eq_zero_of_notMem a b ha hb j hj]
  have heq : ∑ j ∈ S, m j = ∑ j ∈ S ∩ lowBandSpinSet b, m j := by
    symm
    exact Finset.sum_subset Finset.inter_subset_left (fun j hj hnot =>
      hzero j (fun h => hnot (Finset.mem_inter.mpr ⟨hj, h⟩)))
  change (∑ j ∈ S, m j) ≤ _
  rw [heq]
  calc
    _ ≤ ∑ j ∈ lowBandSpinSet b, m j :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun j _ _ => hm j)
    _ ≤ ∑ j ∈ lowBandSpinSet b,
        ((canonicalMarkerReferenceInput a b ha hb j).variation.real univ +
          if j = 0 then 1 else 0) := Finset.sum_le_sum (fun j _ =>
        integral_abs_canonicalMarkerReferenceDirectDensity_le_variation a b ha hb j)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      have hsum : (∑ j ∈ lowBandSpinSet b, if j = 0 then (1 : ℝ) else 0) = 1 := by
        simp [(zero_mem_lowBandSpinSet b).mpr (zero_lt_one.trans_le hb)]
      rw [hsum]
      congr 1
      exact (Finset.sum_coe_sort (lowBandSpinSet b) _).symm

end GapFamily.Construction
