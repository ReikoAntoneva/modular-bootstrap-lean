import GapFamily.Analytic.Kernel.FullKernelScalarColumnSuperposition
import GapFamily.Analytic.Kernel.LowBandThresholdFunctional
import GapFamily.Analytic.Foundation.SignedFubini

/-! Ordinary threshold mass commutes with compact scalar signed input.
The full corrected kernel is integrable on the actual variation-reference
product, including the singular scalar reference row. -/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set Real
open scoped BigOperators

/-- Compact scalar signed input gives ordinary product integrability of the
full corrected kernel on every finite output band. -/
theorem integrable_correctedKernel_scalar_compactInput_lowBand_prod
    (ν : SignedMeasure ℝ) (j : ℤ) (M B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) :
    Integrable (fun p : ℝ × ℝ => correctedKernel j 0 p.2 p.1)
      (ν.variation.prod ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B))) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have hbase := (integrable_const (correctedKernelBound * sqrt M)
    (μ := ν.variation)).mul_prod (lowBand_sqrt_energy_integrable j B)
  apply hbase.mono'
  · exact ((continuous_correctedKernel j 0).comp
      (continuous_snd.prodMk continuous_fst)).aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
      Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem (μ := referenceMeasure j) measurableSet_Ioo)] with p hE he
    exact norm_correctedKernel_scalar_le_sqrt j p.2 p.1 M he.1.le hE.1 hE.2

/-- The ordinary low-band kernel mass is signed-integrable in the input. -/
theorem signedIntegrable_correctedKernel_scalar_lowBandMass
    (ν : SignedMeasure ℝ) (j : ℤ) (M B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) :
    ν.Integrable (fun E => ∫ e, correctedKernel j 0 e E
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  signedIntegrable_integral_of_integrable_prod
    (integrable_correctedKernel_scalar_compactInput_lowBand_prod ν j M B hs)

/-- Fubini identifies the mass of the actual scalar-input signed response. -/
theorem signedIntegral_correctedKernel_scalar_lowBandMass
    (ν : SignedMeasure ℝ) (j : ℤ) (M B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) :
    (∫ᵛ E, (∫ e, correctedKernel j 0 e E
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ∂<•ν) =
      ∫ e, correctedSignedRowResponse ν 0 j e
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) :=
  signedIntegral_integral_swap
    (integrable_correctedKernel_scalar_compactInput_lowBand_prod ν j M B hs)

/-- Every ordinary row mass of the physical scalar column is integrable
against a compact scalar signed input. -/
theorem correctedScalarColumnL1_rowMass_signedIntegrable
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 < B)
    (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) (i : ι) :
    ν.Integrable (fun E => ∫ e,
      correctedScalarColumnL1 J B hB.le (sqrt (E / B) : ℂ) i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) := by
  apply (signedIntegrable_correctedKernel_scalar_lowBandMass ν (J i) M B hs).congr
  filter_upwards [hs] with E hE
  exact (integral_congr_ae (correctedScalarColumnL1_coeFn_physical
    J B hB E hE.1 i)).symm

/-- The actual ordinary row mass commutes with compact scalar column
superposition. -/
theorem signedIntegral_correctedScalarColumnL1_rowMass
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 < B)
    (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) (i : ι) :
    (∫ᵛ E, (∫ e,
      correctedScalarColumnL1 J B hB.le (sqrt (E / B) : ℂ) i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ∂<•ν) =
      ∫ e, correctedSignedRowResponse ν 0 (J i) e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  calc
    _ = ∫ᵛ E, (∫ e, correctedKernel (J i) 0 e E
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ∂<•ν := by
      apply VectorMeasure.integral_congr_ae
      filter_upwards [hs] with E hE
      exact integral_congr_ae (correctedScalarColumnL1_coeFn_physical J B hB E hE.1 i)
    _ = _ := signedIntegral_correctedKernel_scalar_lowBandMass ν (J i) M B hs

/-- The complete finite threshold functional has the actual signed response
mass after compact scalar superposition. -/
theorem signedIntegral_lowBandThresholdFunctional_correctedScalarColumnL1
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 < B)
    (ν : SignedMeasure ℝ) (M : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, 0 ≤ E ∧ E ≤ M) :
    (∫ᵛ E, lowBandThresholdFunctional J B
      (correctedScalarColumnL1 J B hB.le (sqrt (E / B) : ℂ)) ∂<•ν) =
      ∑ i, PoincareScalarFourier.scalarThresholdCoefficient (J i) *
        ∫ e, correctedSignedRowResponse ν 0 (J i) e
          ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  simp_rw [lowBandThresholdFunctional_apply]
  rw [VectorMeasure.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [signedIntegral_const_mul
      (correctedScalarColumnL1_rowMass_signedIntegrable J B hB ν M hs i),
      signedIntegral_correctedScalarColumnL1_rowMass J B hB ν M hs i]
  · intro i hi
    exact (correctedScalarColumnL1_rowMass_signedIntegrable J B hB ν M hs i).const_mul _

end GapFamily.Analytic
