import GapFamily.Analytic.Kernel.FullKernelScalarColumnL1
import GapFamily.Analytic.Kernel.FullKernelSmoothingSignedMeasure
import GapFamily.Analytic.Foundation.SignedFubini
import GapFamily.Analytic.Foundation.L2BochnerIntegral

/-! Scalar columns are superposed using the actual signed Bochner integral.
The input support is compact, while the output scalar row retains its ordinary
physical reference measure, including its singular endpoint. -/

noncomputable section
namespace GapFamily.Analytic

open MeasureTheory Set Real

private theorem continuous_signedIntegrable_of_support_Icc
    {V : Type*} [NormedAddCommGroup V] {f : ℝ → V}
    (hf : Continuous f) (ν : SignedMeasure ℝ) (a b : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, a ≤ E ∧ E ≤ b) : ν.Integrable f := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have hi := hf.integrableOn_Icc (μ := ν.variation) (a := a) (b := b)
  have hr : ν.variation.restrict (Icc a b) = ν.variation :=
    Measure.restrict_eq_self_of_ae_mem hs
  rwa [IntegrableOn, hr] at hi

/-- The physical input energy parametrization is continuous in Hilbert norm. -/
theorem continuous_correctedScalarColumn_physical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    Continuous (fun E : ℝ => correctedScalarColumn J B hB (sqrt (E / B) : ℂ)) :=
  (differentiable_correctedScalarColumn J B hB).continuous.comp (by fun_prop)

/-- A compact signed seed has a genuine Hilbert-valued Bochner column integral. -/
theorem correctedScalarColumn_signedIntegrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) :
    ν.Integrable (fun E => correctedScalarColumn J B hB (sqrt (E / B) : ℂ)) :=
  continuous_signedIntegrable_of_support_Icc
    (continuous_correctedScalarColumn_physical J B hB) ν 0 M hs

/-- The same input parametrization is continuous in the ordinary mass norm. -/
theorem continuous_correctedScalarColumnL1_physical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    Continuous (fun E : ℝ => correctedScalarColumnL1 J B hB (sqrt (E / B) : ℂ)) :=
  (differentiable_correctedScalarColumnL1 J B hB).continuous.comp (by fun_prop)

/-- The ordinary L1 column is also Bochner-integrable against the signed seed. -/
theorem correctedScalarColumnL1_signedIntegrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) :
    ν.Integrable (fun E => correctedScalarColumnL1 J B hB (sqrt (E / B) : ℂ)) :=
  continuous_signedIntegrable_of_support_Icc
    (continuous_correctedScalarColumnL1_physical J B hB) ν 0 M hs

/-- The square-root coordinate reproduces the original nonnegative energy. -/
theorem band_mul_sq_sqrt_div (B E : ℝ) (hB : 0 < B) (hE : 0 ≤ E) :
    B * sqrt (E / B) ^ 2 = E := by
  rw [Real.sq_sqrt (div_nonneg hE hB.le)]
  exact mul_div_cancel₀ E hB.ne'

/-- Physical scalar columns use exactly the full corrected kernel. -/
theorem correctedScalarColumn_coeFn_physical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (E : ℝ) (hE : 0 ≤ E) (i : ι) :
    (correctedScalarColumn J B hB.le (sqrt (E / B) : ℂ) i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        fun e => correctedKernel (J i) 0 e E := by
  simpa only [band_mul_sq_sqrt_div B E hB hE] using
    correctedScalarColumn_coeFn_ofReal J B hB.le (sqrt (E / B))
      (sqrt_nonneg _) i

/-- The ordinary mass realization uses the same physical kernel. -/
theorem correctedScalarColumnL1_coeFn_physical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (E : ℝ) (hE : 0 ≤ E) (i : ι) :
    (correctedScalarColumnL1 J B hB.le (sqrt (E / B) : ℂ) i : ℝ → ℂ) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
        fun e => correctedKernel (J i) 0 e E :=
  (correctedScalarColumnL1_ae J B hB.le (sqrt (E / B)) i).trans
    (correctedScalarColumn_coeFn_physical J B hB E hE i)

/-- On compact scalar-input support the full kernel has an ordinary square-root
output majorant, including on the scalar reference row. -/
theorem norm_correctedKernel_scalar_le_sqrt (j : ℤ) (e E M : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : 0 ≤ E) (hEM : E ≤ M) :
    ‖correctedKernel j 0 e E‖ ≤ correctedKernelBound * sqrt M * sqrt e := by
  have h := norm_correctedKernel_le j 0 e E he (by simpa using hE)
  simp only [Int.cast_zero, abs_zero, mul_zero, zero_add] at h
  calc
    _ ≤ correctedKernelBound * (sqrt e * sqrt E) := h
    _ ≤ correctedKernelBound * (sqrt e * sqrt M) := by
      gcongr
      exact correctedKernelBound_pos.le
    _ = _ := by ring

/-- The compact scalar-input majorant is a genuine output Hilbert function. -/
theorem correctedKernel_scalar_majorant_memLp (j : ℤ) (M B : ℝ) :
    MemLp (fun e : ℝ => correctedKernelBound * sqrt M * sqrt e) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  (lowBand_sqrt_energy_memLp j B).const_mul (correctedKernelBound * sqrt M)

/-- The same majorant also has finite ordinary output mass. -/
theorem correctedKernel_scalar_majorant_integrable (j : ℤ) (M B : ℝ) :
    Integrable (fun e : ℝ => correctedKernelBound * sqrt M * sqrt e)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  (lowBand_sqrt_energy_integrable j B).const_mul (correctedKernelBound * sqrt M)

/-- One Hilbert row of the signed column integral is the actual signed kernel
response. Its identification uses ordinary Fubini for Hilbert test pairings. -/
theorem signedIntegral_correctedScalarColumnRow
    (j : ℤ) (B : ℝ) (hB : 0 < B) (ν : SignedMeasure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) :
    (∫ᵛ E, correctedScalarColumnRow j B hB.le (sqrt (E / B) : ℂ) ∂<•ν) =
      correctedSignedRowResponseLp ν 0 j M B hM hB.le (by simpa using hs) := by
  let μ := (referenceMeasure j).restrict (Ioo |(j : ℝ)| B)
  let := signedMeasure_isFiniteMeasure_variation ν
  have hz : Continuous (fun E : ℝ => (sqrt (E / B) : ℂ)) := by fun_prop
  have hfi : ν.Integrable
      (fun E => correctedScalarColumnRow j B hB.le (sqrt (E / B) : ℂ)) := by
    exact continuous_signedIntegrable_of_support_Icc
      ((differentiable_correctedScalarColumnRow j B hB.le).continuous.comp hz) ν 0 M hs
  have hc : Continuous (fun p : ℝ × ℝ => correctedKernel j 0 p.2 p.1) :=
    (continuous_correctedKernel j 0).comp (f := Prod.swap) continuous_swap
  have hw : Continuous (fun p : ℝ × ℝ => correctedKernelBound * sqrt M * sqrt p.2) := by
    fun_prop
  apply l2_signedIntegral_eq_of_dominated (μ := μ) hfi
    (f := fun E e => correctedKernel j 0 e E)
    (h := fun e => correctedKernelBound * sqrt M * sqrt e)
  · filter_upwards [hs] with E hE
    exact correctedScalarColumn_coeFn_physical (fun _ : Unit => j) B hB E hE.1 ()
  · exact correctedSignedRowResponseLp_coeFn ν 0 j M B hM hB.le (by simpa using hs)
  · exact Filter.Eventually.of_forall fun e =>
      correctedSignedRowResponse_integrable ν 0 j M (by simpa using hs) e
  · exact hc.aestronglyMeasurable
  · exact correctedKernel_scalar_majorant_memLp j M B
  · apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hc.norm.measurable hw.measurable)).mpr
    filter_upwards [hs] with E hE
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
    exact norm_correctedKernel_scalar_le_sqrt j e E M he.1.le hE.1 hE.2

/-- The signed Bochner superposition of the physical scalar columns equals
the existing compact signed-seed Hilbert response, with no replacement kernel. -/
theorem signedIntegral_correctedScalarColumn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (ν : SignedMeasure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) :
    (∫ᵛ E, correctedScalarColumn J B hB.le (sqrt (E / B) : ℂ) ∂<•ν) =
      correctedSignedResponseHilbert (fun _ : Unit => ν) (fun _ => 0) J M B hM hB.le
        (fun _ => by simpa using hs) := by
  apply PiLp.ext
  intro i
  have hi := complexContinuousLinearMap_signedIntegral
    (PiLp.proj 2 (fun k => LowBandRow (J k) B) i)
    (correctedScalarColumn_signedIntegrable J B hB.le ν M hs)
  change (∫ᵛ E, correctedScalarColumn J B hB.le (sqrt (E / B) : ℂ) ∂<•ν) i = _
  simp only [PiLp.proj_apply] at hi
  refine hi.trans ?_
  simpa only [PiLp.proj_apply, correctedScalarColumn_apply,
    correctedSignedResponseHilbert, PiLp.toLp_apply, correctedSignedResponseLp,
    Fintype.sum_unique] using signedIntegral_correctedScalarColumnRow (J i) B hB ν M hM hs

/-- The genuine inverse column is integrable against every compact scalar seed. -/
theorem correctedScalarInverseColumn_signedIntegrable {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) :
    ν.Integrable (fun E => correctedScalarInverseColumn J B hB (sqrt (E / B) : ℂ)) :=
  (correctedLowBandInverse J B).integrable_comp
    (correctedScalarColumn_signedIntegrable J B hB ν M hs)

/-- Applying the actual bounded inverse commutes with the compact signed
superposition. No scalar mass functional is applied to an arbitrary L2 input. -/
theorem signedIntegral_correctedScalarInverseColumn {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B) (ν : SignedMeasure ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) :
    (∫ᵛ E, correctedScalarInverseColumn J B hB.le (sqrt (E / B) : ℂ) ∂<•ν) =
      correctedLowBandInverse J B
        (correctedSignedResponseHilbert (fun _ : Unit => ν) (fun _ => 0) J M B hM hB.le
          (fun _ => by simpa using hs)) := by
  change (∫ᵛ E, correctedLowBandInverse J B
    (correctedScalarColumn J B hB.le (sqrt (E / B) : ℂ)) ∂<•ν) = _
  rw [← complexContinuousLinearMap_signedIntegral (correctedLowBandInverse J B)
    (correctedScalarColumn_signedIntegrable J B hB.le ν M hs),
    signedIntegral_correctedScalarColumn J B hB ν M hM hs]

end GapFamily.Analytic
