import GapFamily.Analytic.Kernel.FullKernelSmoothingSeed
import GapFamily.Analytic.Kernel.FullKernelReality
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# The ordinary signed output of a compact physical seed

Reality identifies the complex kernel integral with its real density.
The induced signed measure is formed only after ordinary integrability has
been proved. Its total variation has the physical cubic band estimate.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GapFamily.Analytic

/-- A genuine signed input has real response, since the actual kernel is real. -/
theorem correctedSignedRowResponse_im (ν : SignedMeasure ℝ) (J j : ℤ)
    (M : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) (e : ℝ) :
    (correctedSignedRowResponse ν J j e).im = 0 := by
  have hi := (correctedSignedRowResponse_integrable ν J j M hs e).re
  have hk : (fun E : ℝ => ((correctedKernel j J e E).re : ℂ)) =
      (fun E : ℝ => correctedKernel j J e E) := by
    funext E
    apply Complex.ext
    · rfl
    · simp
  have h := signedIntegral_complex_ofReal hi
  change (∫ᵛ E, ((correctedKernel j J e E).re : ℂ) ∂<•ν) = _ at h
  rw [hk] at h
  exact congrArg Complex.im h |>.trans (Complex.ofReal_im _)

theorem correctedSignedResponse_im {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) (e : ℝ) :
    (correctedSignedResponse ν J j e).im = 0 := by
  change Complex.imCLM (∑ i, correctedSignedRowResponse (ν i) (J i) j e) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => correctedSignedRowResponse_im (ν i) (J i) j M (hs i) e

theorem correctedSignedResponse_ofReal_re {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) (e : ℝ) :
    ((correctedSignedResponse ν J j e).re : ℂ) = correctedSignedResponse ν J j e := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, correctedSignedResponse_im ν J j M hs e]

/-- The real density as an ordinary `L¹` function, including the scalar output. -/
def correctedSignedResponseL1 {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    Lp ℝ 1 ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  (correctedSignedResponse_integrable_lowBand ν J j M B hs).re.toL1
    (fun e => (correctedSignedResponse ν J j e).re)

theorem correctedSignedResponseL1_coeFn {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    ⇑(correctedSignedResponseL1 ν J j M B hs) =ᵐ[
      (referenceMeasure j).restrict (Ioo |(j : ℝ)| B)]
      (fun e => (correctedSignedResponse ν J j e).re) :=
  (correctedSignedResponse_integrable_lowBand ν J j M B hs).re.coeFn_toL1

/-- The actual induced ordinary signed density measure `μ[rν]` on one row. -/
def correctedSignedOutputMeasure {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) : SignedMeasure ℝ :=
  ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)).withDensityᵥ
    (correctedSignedResponseL1 ν J j M B hs)

theorem correctedSignedOutputMeasure_apply {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (s : Set ℝ) (hset : MeasurableSet s) :
    correctedSignedOutputMeasure ν J j M B hs s =
      ∫ e in s, (correctedSignedResponse ν J j e).re
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
  rw [correctedSignedOutputMeasure, withDensityᵥ_apply (L1.integrable_coeFn _) hset]
  exact integral_congr_ae (correctedSignedResponseL1_coeFn ν J j M B hs).restrict

/-- Exact total variation of the actual ordinary signed output. -/
theorem correctedSignedOutputMeasure_totalVariation {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    (correctedSignedOutputMeasure ν J j M B hs).variation.real univ =
      ∫ e, ‖correctedSignedResponse ν J j e‖
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
  rw [Measure.real, correctedSignedOutputMeasure,
    Measure.variation_withDensityᵥ (L1.integrable_coeFn _),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable _)]
  apply integral_congr_ae
  filter_upwards [correctedSignedResponseL1_coeFn ν J j M B hs] with e he
  rw [he, ← Complex.norm_real, correctedSignedResponse_ofReal_re ν J j M hs e]

/-- Induced output has no scalar-threshold or nonzero-edge atoms. -/
@[simp] theorem correctedSignedOutputMeasure_singleton {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) (e : ℝ) :
    correctedSignedOutputMeasure ν J j M B hs {e} = 0 := by
  rw [correctedSignedOutputMeasure_apply _ _ _ _ _ _ _ (measurableSet_singleton e)]
  simp

/-- The induced ordinary signed output vanishes outside the open low band. -/
theorem correctedSignedOutputMeasure_eq_zero_of_disjoint
    {ι : Type*} [Fintype ι] (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (s : Set ℝ) (hset : MeasurableSet s) (hdis : Disjoint s (Ioo |(j : ℝ)| B)) :
    correctedSignedOutputMeasure ν J j M B hs s = 0 := by
  rw [correctedSignedOutputMeasure_apply _ _ _ _ _ _ _ hset,
    Measure.restrict_restrict hset, hdis.inter_eq, Measure.restrict_empty, integral_zero_measure]

/-- The ordinary total-variation estimate for the actual signed measure output. -/
theorem sum_totalVariation_correctedSignedOutputMeasure_le_physical
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ)
    (hj : Function.Injective j) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ k, |(j k : ℝ)| < B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ 3 * B) :
    (∑ k, (correctedSignedOutputMeasure ν J (j k) (3 * B) B hs).variation.real univ) ≤
      45 * correctedKernelBound * signedSeedMass ν * B ^ 3 := by
  simp_rw [correctedSignedOutputMeasure_totalVariation]
  exact sum_integral_norm_correctedSignedResponse_lowBand_le_physical ν J j hj B hB hband hs

end GapFamily.Analytic
