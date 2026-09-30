import GapFamily.Analytic.Kernel.FullKernelInverseSignedMeasure
import GapFamily.Analytic.Foundation.SignedDensityIntegral

/-!
# Ordinary measure cancellation by the actual inverse

The induced kernel response of the inverse's signed density measure is the
same ordinary integral as the Hilbert response. Consequently the inverse
measure plus its induced measure is exactly the original induced seed
measure on the low band. This is a signed-measure identity, including at
endpoints, with threshold atoms kept separate.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace GapFamily.Analytic

/-- Signed integration of an inverse-density row is the actual Hilbert row response. -/
theorem correctedSignedRowResponse_inverseSignedMeasure
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (hreal : LowBandIsReal J B f) (i : ι) (j : ℤ) (e : ℝ) :
    correctedSignedRowResponse (correctedLowBandInverseSignedMeasure J B hB hunit f hf i)
      (J i) j e =
      correctedKernelRowResponse j (J i) B
        (Ring.inverse (correctedLowBandIdentityPlus J B) f i) e := by
  have hi := correctedSignedRowResponse_integrable
    (correctedLowBandInverseSignedMeasure J B hB hunit f hf i) (J i) j B
    (correctedLowBandInverseSignedMeasure_ae_physical J B hB hunit f hf i) e
  unfold correctedLowBandInverseSignedMeasure at hi
  unfold correctedSignedRowResponse correctedLowBandInverseSignedMeasure
  rw [signedDensity_integral_eq_integral_mul (L1.integrable_coeFn _) hi]
  unfold correctedKernelRowResponse
  apply integral_congr_ae
  filter_upwards [correctedLowBandInverseRealL1_ofReal_ae J B hB hunit f hf hreal i]
    with E hE
  rw [hE]

/-- Finite signed superposition of inverse rows agrees with the full Hilbert response. -/
theorem correctedSignedResponse_inverseSignedMeasure
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (hreal : LowBandIsReal J B f) (j : ℤ) (e : ℝ) :
    correctedSignedResponse (correctedLowBandInverseSignedMeasure J B hB hunit f hf) J j e =
      correctedKernelResponse J B (Ring.inverse (correctedLowBandIdentityPlus J B) f) j e := by
  apply Finset.sum_congr rfl
  intro i hi
  exact correctedSignedRowResponse_inverseSignedMeasure J B hB hunit f hf hreal i j e

/-- The genuine signed inverse measures of a compact seed have the same
response as the genuine Hilbert inverse, at every real observation energy. -/
theorem correctedSignedResponse_correctedSignedInverseMeasure
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (jout : ℤ) (e : ℝ) :
    correctedSignedResponse (correctedSignedInverseMeasure ν J j M B hM hB hs hunit) j jout e =
      correctedKernelResponse j B
        (Ring.inverse (correctedLowBandIdentityPlus j B)
          (correctedSignedResponseHilbert ν J j M B hM hB hs)) jout e :=
  correctedSignedResponse_inverseSignedMeasure j B hB hunit _ _
    (correctedSignedResponseHilbert_isReal ν J j M B hM hB hs) jout e

/-- Exact ordinary signed-measure cancellation for the actual compact-seed inverse. -/
theorem correctedSignedInverseMeasure_add_output
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (k : κ) :
    correctedSignedInverseMeasure ν J j M B hM hB hs hunit k +
      correctedSignedOutputMeasure
        (correctedSignedInverseMeasure ν J j M B hM hB hs hunit) j (j k) B B
        (correctedSignedInverseMeasure_ae_physical ν J j M B hM hB hs hunit) =
      correctedSignedOutputMeasure ν J (j k) M B hs := by
  apply VectorMeasure.ext
  intro s hset
  change correctedSignedInverseMeasure ν J j M B hM hB hs hunit k s +
      correctedSignedOutputMeasure
        (correctedSignedInverseMeasure ν J j M B hM hB hs hunit) j (j k) B B
        (correctedSignedInverseMeasure_ae_physical ν J j M B hM hB hs hunit) s = _
  rw [correctedSignedOutputMeasure_apply _ _ _ _ _ _ _ hset]
  simp_rw [correctedSignedResponse_correctedSignedInverseMeasure ν J j M B hM hB hs hunit]
  exact correctedSignedInverseMeasure_apply_add_response ν J j M B hM hB hs hunit k s hset

/-- Restricting the actual inverse measure to its open physical low band changes nothing. -/
theorem correctedSignedInverseMeasure_restrict_self
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (k : κ) :
    (correctedSignedInverseMeasure ν J j M B hM hB hs hunit k).restrict
      (Ioo |(j k : ℝ)| B) =
      correctedSignedInverseMeasure ν J j M B hM hB hs hunit k := by
  apply VectorMeasure.ext
  intro s hset
  rw [VectorMeasure.restrict_apply _ measurableSet_Ioo hset,
    correctedSignedInverseMeasure_apply _ _ _ _ _ _ _ _ _ _ _ (hset.inter measurableSet_Ioo),
    correctedSignedInverseMeasure_apply _ _ _ _ _ _ _ _ _ _ _ hset,
    Measure.restrict_restrict (hset.inter measurableSet_Ioo),
    Measure.restrict_restrict hset]
  simp only [inter_assoc, inter_self]

end GapFamily.Analytic
