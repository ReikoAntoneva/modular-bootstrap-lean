import GapFamily.Analytic.Kernel.FullKernelInputInverseColumn
import GapFamily.Analytic.Kernel.FullKernelSmoothingSignedMeasure
import GapFamily.Analytic.Kernel.FullKernelResponseFunctional
import GapFamily.Analytic.Foundation.L2BochnerIntegral

/-! Arbitrary physical input columns are superposed by the actual signed
Bochner integral. The input coordinate has unit scale, independently of the
output cutoff, and the inverse commutes with this ordinary superposition.
-/

noncomputable section
namespace GapFamily.Analytic

open MeasureTheory Set Real

private theorem continuous_signedIntegrable_of_compact_support
    {V : Type*} [NormedAddCommGroup V] {f : ℝ → V}
    (hf : Continuous f) (ν : SignedMeasure ℝ) (a b : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, a ≤ E ∧ E ≤ b) : ν.Integrable f := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have hi := hf.integrableOn_Icc (μ := ν.variation) (a := a) (b := b)
  have hr : ν.variation.restrict (Icc a b) = ν.variation :=
    Measure.restrict_eq_self_of_ae_mem hs
  rwa [IntegrableOn, hr] at hi

theorem continuous_correctedInputColumn_physical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) :
    Continuous (fun E : ℝ =>
      correctedInputColumn J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)) :=
  (differentiable_correctedInputColumn J B hB jin).continuous.comp (by fun_prop)

/-- Compact physical signed input gives a genuine Hilbert-valued column integral. -/
theorem correctedInputColumn_signedIntegrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    ν.Integrable (fun E =>
      correctedInputColumn J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)) :=
  continuous_signedIntegrable_of_compact_support
    (continuous_correctedInputColumn_physical J B hB jin) ν |(jin : ℝ)| M hs

theorem continuous_correctedInputColumnL1_physical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) :
    Continuous (fun E : ℝ =>
      correctedInputColumnL1 J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)) :=
  (differentiable_correctedInputColumnL1 J B hB jin).continuous.comp (by fun_prop)

/-- The same physical input is integrable in the ordinary output mass norm. -/
theorem correctedInputColumnL1_signedIntegrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    ν.Integrable (fun E =>
      correctedInputColumnL1 J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)) :=
  continuous_signedIntegrable_of_compact_support
    (continuous_correctedInputColumnL1_physical J B hB jin) ν |(jin : ℝ)| M hs

theorem abs_spin_add_sq_sqrt_sub (jin : ℤ) (E : ℝ) (hE : |(jin : ℝ)| ≤ E) :
    |(jin : ℝ)| + sqrt (E - |(jin : ℝ)|) ^ 2 = E := by
  rw [Real.sq_sqrt (sub_nonneg.mpr hE)]
  ring

/-- The unit-scale coordinate reproduces the literal physical kernel. -/
theorem correctedInputColumn_coeFn_physical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ)
    (E : ℝ) (hE : |(jin : ℝ)| ≤ E) (i : ι) :
    (correctedInputColumn J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ) i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        fun e => correctedKernel (J i) jin e E := by
  simpa only [abs_spin_add_sq_sqrt_sub jin E hE] using
    correctedInputColumn_coeFn_ofReal J B hB jin (sqrt (E - |(jin : ℝ)|))
      (sqrt_nonneg _) i

theorem correctedInputColumnL1_coeFn_physical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ)
    (E : ℝ) (hE : |(jin : ℝ)| ≤ E) (i : ι) :
    (correctedInputColumnL1 J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ) i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        fun e => correctedKernel (J i) jin e E :=
  (correctedInputColumnL1_ae J B hB jin _ i).trans
    (correctedInputColumn_coeFn_physical J B hB jin E hE i)

/-- Compact physical input has an energy-plus-square-root output majorant. -/
theorem norm_correctedKernel_compactInput_le (j jin : ℤ) (e E M : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(jin : ℝ)| ≤ E) (hEM : E ≤ M) :
    ‖correctedKernel j jin e E‖ ≤
      correctedKernelBound * (e * M + sqrt e * sqrt M) := by
  have he0 := (abs_nonneg (j : ℝ)).trans he
  have hC := correctedKernelBound_pos
  calc
    _ ≤ correctedKernelBound * (|(j : ℝ)| * |(jin : ℝ)| + sqrt e * sqrt E) :=
      norm_correctedKernel_le j jin e E he hE
    _ ≤ correctedKernelBound * (e * M + sqrt e * sqrt M) := by
      gcongr
      · exact hE.trans hEM

theorem correctedKernel_compactInput_majorant_memLp (j : ℤ) (M B : ℝ) (hB : 0 ≤ B) :
    MemLp (fun e : ℝ => correctedKernelBound * (e * M + sqrt e * sqrt M)) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  (((lowBand_energy_memLp j B hB).mul_const M).add
    ((lowBand_sqrt_energy_memLp j B).mul_const (sqrt M))).const_mul correctedKernelBound

theorem correctedKernel_compactInput_majorant_integrable (j : ℤ) (M B : ℝ) :
    Integrable (fun e : ℝ => correctedKernelBound * (e * M + sqrt e * sqrt M))
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  (((lowBand_energy_integrable j B).mul_const M).add
    ((lowBand_sqrt_energy_integrable j B).mul_const (sqrt M))).const_mul correctedKernelBound

/-- Each signed Hilbert column integral has the actual ordinary kernel response as representative. -/
theorem signedIntegral_correctedInputColumnRow (j jin : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (ν : SignedMeasure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    (∫ᵛ E, correctedInputColumnRow j jin B hB (sqrt (E - |(jin : ℝ)|) : ℂ) ∂<•ν) =
      correctedSignedRowResponseLp ν jin j M B hM hB hs := by
  let μ := (referenceMeasure j).restrict (Ioo |(j : ℝ)| B)
  let := signedMeasure_isFiniteMeasure_variation ν
  have hz : Continuous (fun E : ℝ => (sqrt (E - |(jin : ℝ)|) : ℂ)) := by fun_prop
  have hfi : ν.Integrable
      (fun E => correctedInputColumnRow j jin B hB (sqrt (E - |(jin : ℝ)|) : ℂ)) :=
    continuous_signedIntegrable_of_compact_support
      ((differentiable_correctedInputColumnRow j jin B hB).continuous.comp hz)
      ν |(jin : ℝ)| M hs
  have hc : Continuous (fun p : ℝ × ℝ => correctedKernel j jin p.2 p.1) :=
    (continuous_correctedKernel j jin).comp (f := Prod.swap) continuous_swap
  have hw : Continuous (fun p : ℝ × ℝ =>
      correctedKernelBound * (p.2 * M + sqrt p.2 * sqrt M)) := by fun_prop
  apply l2_signedIntegral_eq_of_dominated (μ := μ) hfi
    (f := fun E e => correctedKernel j jin e E)
    (h := fun e => correctedKernelBound * (e * M + sqrt e * sqrt M))
  · filter_upwards [hs] with E hE
    exact correctedInputColumn_coeFn_physical (fun _ : Unit => j) B hB jin E hE.1 ()
  · exact correctedSignedRowResponseLp_coeFn ν jin j M B hM hB hs
  · exact Filter.Eventually.of_forall fun e =>
      correctedSignedRowResponse_integrable ν jin j M hs e
  · exact hc.aestronglyMeasurable
  · exact correctedKernel_compactInput_majorant_memLp j M B hB
  · apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hc.norm.measurable hw.measurable)).mpr
    filter_upwards [hs] with E hE
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
    exact norm_correctedKernel_compactInput_le j jin e E M he.1.le hE.1 hE.2

/-- The signed Bochner superposition of arbitrary physical input columns is
the existing genuine compact signed-seed Hilbert response. -/
theorem signedIntegral_correctedInputColumn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ)
    (ν : SignedMeasure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    (∫ᵛ E, correctedInputColumn J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ) ∂<•ν) =
      correctedSignedResponseHilbert (fun _ : Unit => ν) (fun _ => jin) J M B hM hB
        (fun _ => hs) := by
  apply PiLp.ext
  intro i
  have hi := complexContinuousLinearMap_signedIntegral
    (PiLp.proj 2 (fun k => LowBandRow (J k) B) i)
    (correctedInputColumn_signedIntegrable J B hB jin ν M hs)
  change (∫ᵛ E, correctedInputColumn J B hB jin
    (sqrt (E - |(jin : ℝ)|) : ℂ) ∂<•ν) i = _
  simp only [PiLp.proj_apply] at hi
  refine hi.trans ?_
  simpa only [PiLp.proj_apply, correctedInputColumn_apply,
    correctedSignedResponseHilbert, PiLp.toLp_apply, correctedSignedResponseLp,
    Fintype.sum_unique] using signedIntegral_correctedInputColumnRow (J i) jin B hB ν M hM hs

theorem correctedInputInverseColumn_signedIntegrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    ν.Integrable (fun E =>
      correctedInputInverseColumn J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)) :=
  (correctedLowBandInverse J B).integrable_comp
    (correctedInputColumn_signedIntegrable J B hB jin ν M hs)

/-- The actual bounded inverse commutes with arbitrary compact physical signed input. -/
theorem signedIntegral_correctedInputInverseColumn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ)
    (ν : SignedMeasure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    (∫ᵛ E, correctedInputInverseColumn J B hB jin
      (sqrt (E - |(jin : ℝ)|) : ℂ) ∂<•ν) =
      correctedLowBandInverse J B
        (correctedSignedResponseHilbert (fun _ : Unit => ν) (fun _ => jin) J M B hM hB
          (fun _ => hs)) := by
  change (∫ᵛ E, correctedLowBandInverse J B
    (correctedInputColumn J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)) ∂<•ν) = _
  rw [← complexContinuousLinearMap_signedIntegral (correctedLowBandInverse J B)
    (correctedInputColumn_signedIntegrable J B hB jin ν M hs),
    signedIntegral_correctedInputColumn J B hB jin ν M hM hs]

/-- The genuine ordinary-L1 inverse representative is signed-integrable as well. -/
theorem correctedInputInverseColumnL1_signedIntegrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ) (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    ν.Integrable (fun E =>
      correctedInputInverseColumnL1 J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)) :=
  (correctedInputColumnL1_signedIntegrable J B hB jin ν M hs).sub
    ((correctedKernelFiniteSmoothingOperator J J B hB).integrable_comp
      (correctedInputInverseColumn_signedIntegrable J B hB jin ν M hs))

/-- Ordinary-L1 superposition preserves the defining inverse smoothing correction. -/
theorem signedIntegral_correctedInputInverseColumnL1 {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ)
    (ν : SignedMeasure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M) :
    (∫ᵛ E, correctedInputInverseColumnL1 J B hB jin
      (sqrt (E - |(jin : ℝ)|) : ℂ) ∂<•ν) =
      (∫ᵛ E, correctedInputColumnL1 J B hB jin
        (sqrt (E - |(jin : ℝ)|) : ℂ) ∂<•ν) -
      correctedKernelFiniteSmoothingOperator J J B hB
        (correctedLowBandInverse J B
          (correctedSignedResponseHilbert (fun _ : Unit => ν) (fun _ => jin) J M B hM hB
            (fun _ => hs))) := by
  have hi := correctedInputInverseColumn_signedIntegrable J B hB jin ν M hs
  unfold correctedInputInverseColumnL1
  rw [VectorMeasure.integral_fun_sub
    (correctedInputColumnL1_signedIntegrable J B hB jin ν M hs)
    ((correctedKernelFiniteSmoothingOperator J J B hB).integrable_comp hi),
    ← complexContinuousLinearMap_signedIntegral
      (correctedKernelFiniteSmoothingOperator J J B hB) hi,
    signedIntegral_correctedInputInverseColumn J B hB jin ν M hM hs]

/-- The inverse-column response is ordinarily signed-integrable at every physical output. -/
theorem correctedKernelResponse_inputInverseColumn_signedIntegrable
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ)
    (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    ν.Integrable (fun E => correctedKernelResponse J B
      (correctedInputInverseColumn J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)) j e) :=
  (correctedKernelResponseFunctional J B hB j e he).integrable_comp
    (correctedInputInverseColumn_signedIntegrable J B hB jin ν M hs)

/-- Every physical output sees the literal signed superposition of the inverse-column response. -/
theorem signedIntegral_correctedKernelResponse_inputInverseColumn
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (jin : ℤ)
    (ν : SignedMeasure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, |(jin : ℝ)| ≤ E ∧ E ≤ M)
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    (∫ᵛ E, correctedKernelResponse J B
      (correctedInputInverseColumn J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)) j e ∂<•ν) =
      correctedKernelResponse J B
        (correctedLowBandInverse J B
          (correctedSignedResponseHilbert (fun _ : Unit => ν) (fun _ => jin) J M B hM hB
            (fun _ => hs))) j e := by
  change (∫ᵛ E, correctedKernelResponseFunctional J B hB j e he
    (correctedInputInverseColumn J B hB jin (sqrt (E - |(jin : ℝ)|) : ℂ)) ∂<•ν) = _
  rw [← complexContinuousLinearMap_signedIntegral
    (correctedKernelResponseFunctional J B hB j e he)
    (correctedInputInverseColumn_signedIntegrable J B hB jin ν M hs),
    signedIntegral_correctedInputInverseColumn J B hB jin ν M hM hs]
  rfl

end GapFamily.Analytic
