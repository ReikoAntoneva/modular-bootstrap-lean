import GapFamily.Analytic.Kernel.FullKernelInputColumnSuperposition
import GapFamily.Analytic.Kernel.FullKernelFiniteInputColumnSuperposition
import GapFamily.Analytic.Kernel.FullKernelInputInverseColumn
import GapFamily.Analytic.Kernel.FullKernelScalarAnchorPairing
import GapFamily.Analytic.Kernel.LowBandThresholdFunctional
import GapFamily.Analytic.Foundation.SignedFubini

/-! Ordinary low-band mass commutes with compact signed input of any physical
spin. The product bounds retain both the energy and square-root terms and
therefore apply to the singular scalar reference row.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set Real
open scoped BigOperators

/-- Compact physical signed input gives ordinary product integrability of
the actual corrected kernel on every finite output band. -/
theorem integrable_correctedKernel_compactInput_lowBand_prod
    (ν : SignedMeasure ℝ) (j jin : ℤ) (M B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    Integrable (fun p : ℝ × ℝ => correctedKernel j jin p.2 p.1)
      (ν.variation.prod ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B))) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have hbase : Integrable (fun p : ℝ × ℝ =>
      correctedKernelBound * (p.2 * M + sqrt p.2 * sqrt M))
      (ν.variation.prod ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B))) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) (μ := ν.variation)).mul_prod
        (correctedKernel_compactInput_majorant_integrable j M B)
  apply hbase.mono'
  · exact ((continuous_correctedKernel j jin).comp
      (continuous_snd.prodMk continuous_fst)).aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
      Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem (μ := referenceMeasure j) measurableSet_Ioo)] with p hE he
    exact norm_correctedKernel_compactInput_le j jin p.2 p.1 M he.1.le hE.1 hE.2

/-- The ordinary low-band kernel mass is integrable against the actual
variation of the compact physical input. -/
theorem signedIntegrable_correctedKernel_lowBandMass
    (ν : SignedMeasure ℝ) (j jin : ℤ) (M B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    ν.Integrable (fun E => ∫ e, correctedKernel j jin e E
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  signedIntegrable_integral_of_integrable_prod
    (integrable_correctedKernel_compactInput_lowBand_prod ν j jin M B hs)

/-- Ordinary signed Fubini identifies the mass of the genuine input response. -/
theorem signedIntegral_correctedKernel_lowBandMass
    (ν : SignedMeasure ℝ) (j jin : ℤ) (M B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    (∫ᵛ E, (∫ e, correctedKernel j jin e E
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ∂<•ν) =
      ∫ e, correctedSignedRowResponse ν jin j e
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) :=
  signedIntegral_integral_swap
    (integrable_correctedKernel_compactInput_lowBand_prod ν j jin M B hs)

/-- Every ordinary row mass of the physical input column is integrable
against its compact physical signed input. -/
theorem correctedInputColumnL1_rowMass_signedIntegrable
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) (i : ι) :
    ν.Integrable (fun E => ∫ e,
      correctedInputColumnL1 J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ) i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) := by
  apply (signedIntegrable_correctedKernel_lowBandMass ν (J i) jin M B hs).congr
  filter_upwards [hs] with E hE
  exact (integral_congr_ae (correctedInputColumnL1_coeFn_physical
    J B hB jin E hE.1 i)).symm

/-- Actual ordinary row mass commutes with compact input-column superposition. -/
theorem signedIntegral_correctedInputColumnL1_rowMass
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) (i : ι) :
    (∫ᵛ E, (∫ e,
      correctedInputColumnL1 J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ) i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ∂<•ν) =
      ∫ e, correctedSignedRowResponse ν jin (J i) e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  calc
    _ = ∫ᵛ E, (∫ e, correctedKernel (J i) jin e E
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ∂<•ν := by
      apply VectorMeasure.integral_congr_ae
      filter_upwards [hs] with E hE
      exact integral_congr_ae (correctedInputColumnL1_coeFn_physical
        J B hB jin E hE.1 i)
    _ = _ := signedIntegral_correctedKernel_lowBandMass ν (J i) jin M B hs

/-- The complete bounded L1 threshold functional has the actual signed
response mass after compact arbitrary-spin column superposition. -/
theorem signedIntegral_lowBandThresholdFunctional_correctedInputColumnL1
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    (∫ᵛ E, lowBandThresholdFunctional J B
      (correctedInputColumnL1 J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)) ∂<•ν) =
      ∑ i, PoincareScalarFourier.scalarThresholdCoefficient (J i) *
        ∫ e, correctedSignedRowResponse ν jin (J i) e
          ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  simp_rw [lowBandThresholdFunctional_apply]
  rw [VectorMeasure.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [signedIntegral_const_mul
      (correctedInputColumnL1_rowMass_signedIntegrable J B hB jin ν M hs i),
      signedIntegral_correctedInputColumnL1_rowMass J B hB jin ν M hs i]
  · intro i hi
    exact (correctedInputColumnL1_rowMass_signedIntegrable J B hB jin ν M hs i).const_mul _

/-- The inverse threshold expression is integrable against every compact
physical input, using only the bounded L1 and smoothing mass maps. -/
theorem correctedInputInverseThreshold_signedIntegrable
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    ν.Integrable (fun E => correctedInputInverseThreshold J B hB jin
      (sqrt (E - |(jin : ℝ)|) : ℂ)) := by
  let T := (correctedSmoothingThresholdFunctional J B hB).comp
    (Ring.inverse (correctedLowBandIdentityPlus J B))
  have hF := correctedInputColumn_signedIntegrable J B hB jin ν M hs
  have hG := (lowBandThresholdFunctional J B).integrable_comp
    (correctedInputColumnL1_signedIntegrable J B hB jin ν M hs)
  exact hG.sub (T.integrable_comp hF)

/-- The actual inverse measure's weighted threshold mass is the ordinary
signed pairing with the arbitrary-spin input inverse threshold column. -/
theorem correctedInputInverseThreshold_signedIntegral
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (ν : SignedMeasure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) :
    (∑ i, (PoincareScalarFourier.scalarThresholdCoefficient (J i)).re *
      correctedSignedInverseMeasure (fun _ : Unit => ν) (fun _ => jin)
        J M B hM hB (fun _ => hs) hunit i univ) =
      ∫ᵛ E, (correctedInputInverseThreshold J B hB jin
        (sqrt (E - |(jin : ℝ)|) : ℂ)).re ∂<•ν := by
  let f := correctedSignedResponseHilbert (fun _ : Unit => ν) (fun _ => jin)
    J M B hM hB (fun _ => hs)
  let T := (correctedSmoothingThresholdFunctional J B hB).comp
    (Ring.inverse (correctedLowBandIdentityPlus J B))
  let F := fun E : ℝ => correctedInputColumn J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)
  let G := fun E : ℝ => lowBandThresholdFunctional J B
    (correctedInputColumnL1 J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ))
  have hF : ν.Integrable F := correctedInputColumn_signedIntegrable J B hB jin ν M hs
  have hG : ν.Integrable G := (lowBandThresholdFunctional J B).integrable_comp
    (correctedInputColumnL1_signedIntegrable J B hB jin ν M hs)
  have hT : ν.Integrable (fun E => T (F E)) := T.integrable_comp hF
  have hZ := correctedInputInverseThreshold_signedIntegrable J B hB jin ν M hs
  have hsuper : (∫ᵛ E, F E ∂<•ν) = f :=
    signedIntegral_correctedInputColumn J B hB jin ν M hM hs
  have hmass : (∫ᵛ E, G E ∂<•ν) =
      ∑ i, PoincareScalarFourier.scalarThresholdCoefficient (J i) * ∫ e, f i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
    rw [signedIntegral_lowBandThresholdFunctional_correctedInputColumnL1
      J B hB jin ν M hs]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply integral_congr_ae
    filter_upwards [correctedSignedResponseLp_coeFn (fun _ : Unit => ν) (fun _ => jin)
      (J i) M B hM hB (fun _ => hs)] with e he
    change correctedSignedRowResponse ν jin (J i) e =
      correctedSignedResponseLp (fun _ : Unit => ν) (fun _ => jin)
        (J i) M B hM hB (fun _ => hs) e
    simpa only [correctedSignedResponse, Fintype.sum_unique] using he.symm
  have hzint : (∫ᵛ E, correctedInputInverseThreshold J B hB jin
      (sqrt (E - |(jin : ℝ)|) : ℂ) ∂<•ν) = (∫ᵛ E, G E ∂<•ν) - T f := by
    change (∫ᵛ E, G E - T (F E) ∂<•ν) = _
    rw [VectorMeasure.integral_fun_sub (f := G) (g := fun E => T (F E)) hG hT,
      ← complexContinuousLinearMap_signedIntegral T hF, hsuper]
  rw [← signedIntegral_re hZ, hzint, hmass]
  change (∑ i, (PoincareScalarFourier.scalarThresholdCoefficient (J i)).re *
    correctedLowBandInverseSignedMeasure J B hB hunit f
      (correctedSignedResponseHilbert_integrable (fun _ : Unit => ν) (fun _ => jin)
        J M B hM hB (fun _ => hs)) i univ) = _
  rw [correctedLowBandInverseSignedMeasure_threshold_eq]
  rfl

/-- Finite arbitrary-spin input superposition commutes with the ordinary
threshold mass of the corrected kernel response. -/
theorem sum_signedIntegral_lowBandThresholdFunctional_correctedInputColumnL1
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (ν : κ → SignedMeasure ℝ) (jin : κ → ℤ) (J : ι → ℤ) (M B : ℝ) (hB : 0 ≤ B)
    (hs : ∀ k, ∀ᵐ E ∂(ν k).variation, |(jin k : ℝ)| ≤ E ∧ E ≤ M) :
    (∑ k, ∫ᵛ E, lowBandThresholdFunctional J B
      (correctedInputColumnL1 J B hB (jin k) (sqrt (E - |(jin k : ℝ)|) : ℂ)) ∂<•ν k) =
      ∑ i, PoincareScalarFourier.scalarThresholdCoefficient (J i) *
        ∫ e, correctedSignedResponse ν jin (J i) e
          ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  classical
  calc
    _ = ∑ k, ∑ i, PoincareScalarFourier.scalarThresholdCoefficient (J i) *
        ∫ e, correctedSignedRowResponse (ν k) (jin k) (J i) e
          ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) :=
      Finset.sum_congr rfl fun k _ =>
        signedIntegral_lowBandThresholdFunctional_correctedInputColumnL1
          J B hB (jin k) (ν k) M (hs k)
    _ = ∑ i, ∑ k, PoincareScalarFourier.scalarThresholdCoefficient (J i) *
        ∫ e, correctedSignedRowResponse (ν k) (jin k) (J i) e
          ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum]
      congr 1
      exact (integral_finsetSum Finset.univ fun k _ =>
        correctedSignedRowResponse_integrable_lowBand (ν k) (jin k) (J i) M B (hs k)).symm

/-- The finite sum of the genuine input inverse-threshold pairings equals
the weighted ordinary mass of the actual finite-input inverse measure. -/
theorem sum_signedIntegral_correctedInputInverseThreshold
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (ν : κ → SignedMeasure ℝ) (jin : κ → ℤ) (J : ι → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ k, ∀ᵐ E ∂(ν k).variation, |(jin k : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) :
    (∑ k, ∫ᵛ E, (correctedInputInverseThreshold J B hB (jin k)
      (sqrt (E - |(jin k : ℝ)|) : ℂ)).re ∂<•ν k) =
      ∑ i, (PoincareScalarFourier.scalarThresholdCoefficient (J i)).re *
        correctedSignedInverseMeasure ν jin J M B hM hB hs hunit i univ := by
  classical
  let f := correctedSignedResponseHilbert ν jin J M B hM hB hs
  let T := (correctedSmoothingThresholdFunctional J B hB).comp
    (Ring.inverse (correctedLowBandIdentityPlus J B))
  let F := fun (k : κ) (E : ℝ) =>
    correctedInputColumn J B hB (jin k) (sqrt (E - |(jin k : ℝ)|) : ℂ)
  let G := fun (k : κ) (E : ℝ) => lowBandThresholdFunctional J B
    (correctedInputColumnL1 J B hB (jin k) (sqrt (E - |(jin k : ℝ)|) : ℂ))
  have hF (k : κ) : (ν k).Integrable (F k) :=
    correctedInputColumn_signedIntegrable J B hB (jin k) (ν k) M (hs k)
  have hG (k : κ) : (ν k).Integrable (G k) :=
    (lowBandThresholdFunctional J B).integrable_comp
      (correctedInputColumnL1_signedIntegrable J B hB (jin k) (ν k) M (hs k))
  have hpart (k : κ) : (∫ᵛ E, correctedInputInverseThreshold J B hB (jin k)
      (sqrt (E - |(jin k : ℝ)|) : ℂ) ∂<•ν k) =
      (∫ᵛ E, G k E ∂<•ν k) - T (∫ᵛ E, F k E ∂<•ν k) := by
    change (∫ᵛ E, G k E - T (F k E) ∂<•ν k) = _
    rw [VectorMeasure.integral_fun_sub (f := G k) (g := fun E => T (F k E))
      (hG k) (T.integrable_comp (hF k)),
      ← complexContinuousLinearMap_signedIntegral T (hF k)]
  have hsuper : (∑ k, ∫ᵛ E, F k E ∂<•ν k) = f :=
    sum_signedIntegral_correctedInputColumn ν jin J M B hM hB hs
  have hzint : (∑ k, ∫ᵛ E, correctedInputInverseThreshold J B hB (jin k)
      (sqrt (E - |(jin k : ℝ)|) : ℂ) ∂<•ν k) =
      (∑ k, ∫ᵛ E, G k E ∂<•ν k) - T f := by
    simp_rw [hpart]
    rw [Finset.sum_sub_distrib, ← map_sum, hsuper]
  have hmass : (∑ k, ∫ᵛ E, G k E ∂<•ν k) =
      ∑ i, PoincareScalarFourier.scalarThresholdCoefficient (J i) * ∫ e, f i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
    rw [sum_signedIntegral_lowBandThresholdFunctional_correctedInputColumnL1
      ν jin J M B hB hs]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact integral_congr_ae (correctedSignedResponseLp_coeFn ν jin (J i) M B hM hB hs).symm
  have hre : (∑ k, ∫ᵛ E, (correctedInputInverseThreshold J B hB (jin k)
      (sqrt (E - |(jin k : ℝ)|) : ℂ)).re ∂<•ν k) =
      (∑ k, ∫ᵛ E, correctedInputInverseThreshold J B hB (jin k)
        (sqrt (E - |(jin k : ℝ)|) : ℂ) ∂<•ν k).re := by
    conv_rhs => rw [← Complex.reCLM_apply, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact (signedIntegral_re
      (correctedInputInverseThreshold_signedIntegrable J B hB (jin k) (ν k) M (hs k))).symm
  rw [hre, hzint, hmass]
  change _ = ∑ i, (PoincareScalarFourier.scalarThresholdCoefficient (J i)).re *
    correctedLowBandInverseSignedMeasure J B hB hunit f
      (correctedSignedResponseHilbert_integrable ν jin J M B hM hB hs) i univ
  rw [correctedLowBandInverseSignedMeasure_threshold_eq]
  rfl

end GapFamily.Analytic
