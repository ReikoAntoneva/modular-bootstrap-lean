import GapFamily.Analytic.Kernel.FullKernelInverseSmoothing
import GapFamily.Analytic.Kernel.FullKernelConjugation
import GapFamily.Analytic.Kernel.FullKernelSmoothingSignedMeasure

/-!
# The ordinary signed measure of the actual inverse

Rowwise ordinary integrability and reality give actual signed density measures
for the inverse of the full identity-plus operator. Their total variation is
the ordinary absolute integral, including on the scalar row.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GapFamily.Analytic

variable {ι : Type*} [Fintype ι]

/-- The real part of the actual inverse as an ordinary `L¹` equivalence class. -/
def correctedLowBandInverseRealL1 (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) (i : ι) :
    Lp ℝ 1 ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) :=
  (correctedLowBandInverse_integrable J B hB hunit f hf i).re.toL1
    (fun E => ((Ring.inverse (correctedLowBandIdentityPlus J B) f) i E).re)

theorem correctedLowBandInverseRealL1_coeFn (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) (i : ι) :
    ⇑(correctedLowBandInverseRealL1 J B hB hunit f hf i) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
      (fun E => ((Ring.inverse (correctedLowBandIdentityPlus J B) f) i E).re) :=
  (correctedLowBandInverse_integrable J B hB hunit f hf i).re.coeFn_toL1

/-- The inverse induces an ordinary signed density measure on each open band. -/
def correctedLowBandInverseSignedMeasure (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) (i : ι) :
    SignedMeasure ℝ :=
  ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)).withDensityᵥ
    (correctedLowBandInverseRealL1 J B hB hunit f hf i)

theorem correctedLowBandInverseSignedMeasure_apply (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) (i : ι)
    (s : Set ℝ) (hs : MeasurableSet s) :
    correctedLowBandInverseSignedMeasure J B hB hunit f hf i s =
      ∫ E in s, ((Ring.inverse (correctedLowBandIdentityPlus J B) f) i E).re
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  rw [correctedLowBandInverseSignedMeasure,
    withDensityᵥ_apply (L1.integrable_coeFn _) hs]
  exact integral_congr_ae
    (correctedLowBandInverseRealL1_coeFn J B hB hunit f hf i).restrict

/-- For real input, the signed density is the full complex inverse almost everywhere. -/
theorem correctedLowBandInverseRealL1_ofReal_ae (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (hreal : LowBandIsReal J B f) (i : ι) :
    (fun E => (correctedLowBandInverseRealL1 J B hB hunit f hf i E : ℂ)) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
      ((Ring.inverse (correctedLowBandIdentityPlus J B) f) i) := by
  have hr := (lowBandIsReal_iff_im_zero_ae J B _).mp
    (hreal.correctedLowBandInverse J B hunit) i
  filter_upwards [correctedLowBandInverseRealL1_coeFn J B hB hunit f hf i, hr]
    with E hE hrE
  rw [hE]
  apply Complex.ext
  · rfl
  · simpa using hrE.symm

/-- The actual inverse measure obeys its ordinary integral equation on every measurable set. -/
theorem correctedLowBandInverseSignedMeasure_apply_eq_sub
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) (i : ι)
    (s : Set ℝ) (hs : MeasurableSet s) :
    correctedLowBandInverseSignedMeasure J B hB hunit f hf i s =
      (∫ E in s, (f i E).re
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) -
      ∫ E in s, (correctedKernelResponse J B
        (Ring.inverse (correctedLowBandIdentityPlus J B) f) (J i) E).re
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  rw [correctedLowBandInverseSignedMeasure_apply J B hB hunit f hf i s hs]
  calc
    _ = ∫ E in s, ((f i E).re - (correctedKernelResponse J B
        (Ring.inverse (correctedLowBandIdentityPlus J B) f) (J i) E).re)
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
      apply integral_congr_ae
      filter_upwards [(correctedLowBandInverse_coeFn_eq_sub J B hunit f i).restrict,
        (correctedLowBandOperator_coeFn J B hB
          (Ring.inverse (correctedLowBandIdentityPlus J B) f) i).restrict] with E hinv hkernel
      rw [hinv, hkernel, Complex.sub_re]
    _ = _ := integral_sub (hf i).re.integrableOn
      (correctedKernelResponse_integrable_lowBand J B hB
        (Ring.inverse (correctedLowBandIdentityPlus J B) f) (J i)).re.integrableOn

/-- Exact total variation of the real actual inverse on one physical row. -/
theorem correctedLowBandInverseSignedMeasure_totalVariation
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (hreal : LowBandIsReal J B f) (i : ι) :
    (correctedLowBandInverseSignedMeasure J B hB hunit f hf i).variation.real univ =
      ∫ E, ‖(Ring.inverse (correctedLowBandIdentityPlus J B) f) i E‖
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  rw [Measure.real, correctedLowBandInverseSignedMeasure,
    Measure.variation_withDensityᵥ (L1.integrable_coeFn _),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable _)]
  apply integral_congr_ae
  filter_upwards [correctedLowBandInverseRealL1_ofReal_ae J B hB hunit f hf hreal i]
    with E hE
  rw [← Complex.norm_real, hE]

/-- The actual inverse measure satisfies the ordinary smoothing estimate. -/
theorem correctedLowBandInverseSignedMeasure_totalVariation_le
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (hreal : LowBandIsReal J B f) (i : ι) :
    (correctedLowBandInverseSignedMeasure J B hB hunit f hf i).variation.real univ ≤
      (∫ E, ‖f i E‖ ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) +
        correctedSmoothingBound B * Real.sqrt (Fintype.card ι : ℝ) *
          ‖Ring.inverse (correctedLowBandIdentityPlus J B)‖ * ‖f‖ := by
  rw [correctedLowBandInverseSignedMeasure_totalVariation J B hB hunit f hf hreal i]
  exact integral_norm_correctedLowBandInverse_le J B hB hunit f hf i

/-- The inverse's ordinary density does not create threshold or edge atoms. -/
@[simp] theorem correctedLowBandInverseSignedMeasure_singleton
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) (i : ι) (E : ℝ) :
    correctedLowBandInverseSignedMeasure J B hB hunit f hf i {E} = 0 := by
  rw [correctedLowBandInverseSignedMeasure_apply _ _ _ _ _ _ _ _
    (measurableSet_singleton E)]
  simp

/-- The inverse's ordinary measure vanishes away from the open low band. -/
theorem correctedLowBandInverseSignedMeasure_eq_zero_of_disjoint
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) (i : ι)
    (s : Set ℝ) (hs : MeasurableSet s) (hdis : Disjoint s (Ioo |(J i : ℝ)| B)) :
    correctedLowBandInverseSignedMeasure J B hB hunit f hf i s = 0 := by
  rw [correctedLowBandInverseSignedMeasure_apply _ _ _ _ _ _ _ _ hs,
    Measure.restrict_restrict hs, hdis.inter_eq, Measure.restrict_empty, integral_zero_measure]

/-- The variation of an inverse density is absolutely continuous for its physical band measure. -/
theorem correctedLowBandInverseSignedMeasure_variation_absolutelyContinuous
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) (i : ι) :
    (correctedLowBandInverseSignedMeasure J B hB hunit f hf i).variation ≪
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  rw [correctedLowBandInverseSignedMeasure,
    Measure.variation_withDensityᵥ (L1.integrable_coeFn _)]
  exact withDensity_absolutelyContinuous _ _

/-- Actual variation is carried by the open band, not merely by cancellation of signed mass. -/
theorem correctedLowBandInverseSignedMeasure_ae_mem
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) (i : ι) :
    ∀ᵐ E ∂(correctedLowBandInverseSignedMeasure J B hB hunit f hf i).variation,
      E ∈ Ioo |(J i : ℝ)| B :=
  (correctedLowBandInverseSignedMeasure_variation_absolutelyContinuous
    J B hB hunit f hf i).ae_le (ae_restrict_mem measurableSet_Ioo)

/-- The actual inverse variation has the physical compact-support bound. -/
theorem correctedLowBandInverseSignedMeasure_ae_physical
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) (i : ι) :
    ∀ᵐ E ∂(correctedLowBandInverseSignedMeasure J B hB hunit f hf i).variation,
      |(J i : ℝ)| ≤ E ∧ E ≤ B :=
  (correctedLowBandInverseSignedMeasure_ae_mem J B hB hunit f hf i).mono
    (fun _ hE => ⟨hE.1.le, hE.2.le⟩)

/-- Reality of the actual signed kernel integral gives reality of its Hilbert class. -/
theorem correctedSignedResponseHilbert_isReal {κ : Type*} [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    LowBandIsReal j B (correctedSignedResponseHilbert ν J j M B hM hB hs) := by
  apply (lowBandIsReal_iff_im_zero_ae j B _).mpr
  intro k
  filter_upwards [correctedSignedResponseLp_coeFn ν J (j k) M B hM hB hs] with E hE
  change ((correctedSignedResponseLp ν J (j k) M B hM hB hs) E).im = 0
  rw [hE]
  exact correctedSignedResponse_im ν J (j k) M hs E

/-- The actual signed measure obtained by applying the full inverse to a compact seed response. -/
def correctedSignedInverseMeasure {κ : Type*} [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (k : κ) : SignedMeasure ℝ :=
  correctedLowBandInverseSignedMeasure j B hB hunit
    (correctedSignedResponseHilbert ν J j M B hM hB hs)
    (correctedSignedResponseHilbert_integrable ν J j M B hM hB hs) k

theorem correctedSignedInverseMeasure_apply {κ : Type*} [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (k : κ)
    (s : Set ℝ) (hset : MeasurableSet s) :
    correctedSignedInverseMeasure ν J j M B hM hB hs hunit k s =
      ∫ E in s, ((Ring.inverse (correctedLowBandIdentityPlus j B)
        (correctedSignedResponseHilbert ν J j M B hM hB hs)) k E).re
        ∂(referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B) :=
  correctedLowBandInverseSignedMeasure_apply j B hB hunit _ _ k s hset

/-- Its exact variation is that of the full complex Hilbert inverse. -/
theorem correctedSignedInverseMeasure_totalVariation {κ : Type*} [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (k : κ) :
    (correctedSignedInverseMeasure ν J j M B hM hB hs hunit k).variation.real univ =
      ∫ E, ‖(Ring.inverse (correctedLowBandIdentityPlus j B)
        (correctedSignedResponseHilbert ν J j M B hM hB hs)) k E‖
        ∂(referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B) :=
  correctedLowBandInverseSignedMeasure_totalVariation j B hB hunit _ _
    (correctedSignedResponseHilbert_isReal ν J j M B hM hB hs) k

/-- The signed inverse and its actual kernel correction reproduce the original signed response. -/
theorem correctedSignedInverseMeasure_apply_add_response {κ : Type*} [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (k : κ)
    (s : Set ℝ) (hset : MeasurableSet s) :
    correctedSignedInverseMeasure ν J j M B hM hB hs hunit k s +
      (∫ E in s, (correctedKernelResponse j B
        (Ring.inverse (correctedLowBandIdentityPlus j B)
          (correctedSignedResponseHilbert ν J j M B hM hB hs)) (j k) E).re
        ∂(referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B)) =
      correctedSignedOutputMeasure ν J (j k) M B hs s := by
  rw [correctedSignedInverseMeasure,
    correctedLowBandInverseSignedMeasure_apply_eq_sub j B hB hunit _ _ k s hset,
    sub_add_cancel, correctedSignedOutputMeasure_apply ν J (j k) M B hs s hset]
  apply integral_congr_ae
  filter_upwards [(correctedSignedResponseLp_coeFn ν J (j k) M B hM hB hs).restrict]
    with E hE
  exact congrArg Complex.re hE

/-- No ordinary signed inverse response creates an atom, including at the scalar threshold. -/
@[simp] theorem correctedSignedInverseMeasure_singleton {κ : Type*} [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (k : κ) (E : ℝ) :
    correctedSignedInverseMeasure ν J j M B hM hB hs hunit k {E} = 0 :=
  correctedLowBandInverseSignedMeasure_singleton j B hB hunit _ _ k E

/-- Compact-seed inverse measures are supported on the same open output band. -/
theorem correctedSignedInverseMeasure_eq_zero_of_disjoint {κ : Type*} [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (k : κ)
    (s : Set ℝ) (hset : MeasurableSet s) (hdis : Disjoint s (Ioo |(j k : ℝ)| B)) :
    correctedSignedInverseMeasure ν J j M B hM hB hs hunit k s = 0 :=
  correctedLowBandInverseSignedMeasure_eq_zero_of_disjoint j B hB hunit _ _ k s hset hdis

/-- Compact-seed inverse variation is carried by the physical compact interval. -/
theorem correctedSignedInverseMeasure_ae_physical {κ : Type*} [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (k : κ) :
    ∀ᵐ E ∂(correctedSignedInverseMeasure ν J j M B hM hB hs hunit k).variation,
      |(j k : ℝ)| ≤ E ∧ E ≤ B :=
  (correctedLowBandInverseSignedMeasure_ae_mem j B hB hunit _ _ k).mono
    (fun _ hE => ⟨hE.1.le, hE.2.le⟩)

/-- The physical inverse TV bound retains the actual inverse norm and the genuine seed mass. -/
theorem sum_totalVariation_correctedSignedInverseMeasure_le_physical
    {κ : Type*} [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ)
    (hj : Function.Injective j) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ k, |(j k : ℝ)| < B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ 3 * B)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) :
    (∑ k, (correctedSignedInverseMeasure ν J j (3 * B) B
      (by linarith) (by linarith) hs hunit k).variation.real univ) ≤
      (45 * correctedKernelBound * B ^ 3 +
        500 * correctedKernelBound ^ 2 * B ^ 6 *
          ‖Ring.inverse (correctedLowBandIdentityPlus j B)‖) * signedSeedMass ν := by
  simp_rw [correctedSignedInverseMeasure_totalVariation]
  exact sum_integral_norm_correctedLowBandInverse_signedSeed_le_physical
    ν J j hj B hB hband hs hunit

end GapFamily.Analytic
