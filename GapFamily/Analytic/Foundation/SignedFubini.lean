import GapFamily.Analytic.Foundation.SignedMomentIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! Ordinary Fubini for a finite signed input measure.
All absolute-integrability hypotheses use the actual variation measure.
The signed integral is its proved Jordan difference, and both iterated
integrals are shown integrable before their order is exchanged.
-/
noncomputable section
namespace GapFamily.Analytic

open MeasureTheory Function Filter
open scoped ENNReal Topology

/-- The positive Jordan part is dominated by the actual variation measure. -/
theorem signedMeasure_posPart_le_variation (ν : SignedMeasure ℝ) :
    ν.toJordanDecomposition.posPart ≤ ν.variation := by
  rw [← SignedMeasure.totalVariation_eq_variation, SignedMeasure.totalVariation]
  exact Measure.le_add_right le_rfl

/-- The negative Jordan part is dominated by the actual variation measure. -/
theorem signedMeasure_negPart_le_variation (ν : SignedMeasure ℝ) :
    ν.toJordanDecomposition.negPart ≤ ν.variation := by
  rw [← SignedMeasure.totalVariation_eq_variation, SignedMeasure.totalVariation]
  exact Measure.le_add_left le_rfl

variable {ν : SignedMeasure ℝ} {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℝ → ℂ}

/-- Product absolute integrability supplies signed-integrable input slices
for almost every output energy. -/
theorem ae_signedIntegrable_of_integrable_prod
    (hf : Integrable (uncurry f) (ν.variation.prod μ)) :
    ∀ᵐ e ∂μ, ν.Integrable (fun E => f E e) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  exact hf.prod_left_ae

/-- Product absolute integrability supplies ordinary output slices for
almost every input energy under the variation measure. -/
theorem ae_integrable_of_signed_integrable_prod
    (hf : Integrable (uncurry f) (ν.variation.prod μ)) :
    ∀ᵐ E ∂ν.variation, Integrable (f E) μ := by
  let := signedMeasure_isFiniteMeasure_variation ν
  exact hf.prod_right_ae

/-- Integrating the output variable first gives an actual signed-integrable
function of the input energy. -/
theorem signedIntegrable_integral_of_integrable_prod
    (hf : Integrable (uncurry f) (ν.variation.prod μ)) :
    ν.Integrable (fun E => ∫ e, f E e ∂μ) :=
  hf.integral_prod_left

/-- The input signed integral is ordinarily integrable in the output variable. -/
theorem integrable_signedIntegral_of_integrable_prod
    (hf : Integrable (uncurry f) (ν.variation.prod μ)) :
    Integrable (fun e => ∫ᵛ E, f E e ∂<•ν) μ := by
  have hp : Integrable (uncurry f) (ν.toJordanDecomposition.posPart.prod μ) :=
    hf.mono_measure (Measure.prod_mono (signedMeasure_posPart_le_variation ν) le_rfl)
  have hn : Integrable (uncurry f) (ν.toJordanDecomposition.negPart.prod μ) :=
    hf.mono_measure (Measure.prod_mono (signedMeasure_negPart_le_variation ν) le_rfl)
  apply (hp.integral_prod_right.sub hn.integral_prod_right).congr
  filter_upwards [ae_signedIntegrable_of_integrable_prod hf] with e he
  exact (signedIntegral_eq_jordan he).symm

/-- Fubini for the actual signed input integral and an ordinary output measure.
The single product-integrability hypothesis includes every convergence condition. -/
theorem signedIntegral_integral_swap
    (hf : Integrable (uncurry f) (ν.variation.prod μ)) :
    (∫ᵛ E, (∫ e, f E e ∂μ) ∂<•ν) =
      ∫ e, (∫ᵛ E, f E e ∂<•ν) ∂μ := by
  have hp : Integrable (uncurry f) (ν.toJordanDecomposition.posPart.prod μ) :=
    hf.mono_measure (Measure.prod_mono (signedMeasure_posPart_le_variation ν) le_rfl)
  have hn : Integrable (uncurry f) (ν.toJordanDecomposition.negPart.prod μ) :=
    hf.mono_measure (Measure.prod_mono (signedMeasure_negPart_le_variation ν) le_rfl)
  have hip : Integrable (fun e => ∫ E, f E e ∂ν.toJordanDecomposition.posPart) μ :=
    hp.integral_prod_right
  have hin : Integrable (fun e => ∫ E, f E e ∂ν.toJordanDecomposition.negPart) μ :=
    hn.integral_prod_right
  rw [signedIntegral_eq_jordan (signedIntegrable_integral_of_integrable_prod hf),
    integral_integral_swap hp, integral_integral_swap hn,
    ← integral_sub hip hin]
  apply integral_congr_ae
  filter_upwards [ae_signedIntegrable_of_integrable_prod hf] with e he
  exact (signedIntegral_eq_jordan he).symm

section Series

variable {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ}

omit [Countable ι] in
private theorem tsum_lintegral_enorm_variation_ne_top
    (hi : ∀ i, ν.Integrable (F i))
    (hs : Summable (fun i => ∫ E, ‖F i E‖ ∂ν.variation)) :
    (∑' i, ∫⁻ E, ‖F i E‖ₑ ∂ν.variation) ≠ ∞ := by
  have he (i : ι) : (∫⁻ E, ‖F i E‖ₑ ∂ν.variation) =
      ENNReal.ofReal (∫ E, ‖F i E‖ ∂ν.variation) :=
    (ofReal_integral_norm_eq_lintegral_enorm (hi i)).symm
  simpa only [he] using hs.tsum_ofReal_ne_top

/-- A countable family with summable variation norm integrals is absolutely
summable at almost every input energy. -/
theorem ae_summable_norm_of_summable_variation_integral_norm
    (hi : ∀ i, ν.Integrable (F i))
    (hs : Summable (fun i => ∫ E, ‖F i E‖ ∂ν.variation)) :
    ∀ᵐ E ∂ν.variation, Summable (fun i => ‖F i E‖) := by
  have hfinite := tsum_lintegral_enorm_variation_ne_top hi hs
  rw [← lintegral_tsum (fun i => (hi i).aestronglyMeasurable.enorm)] at hfinite
  have hae := ae_lt_top'
    (AEMeasurable.tsum (fun i => (hi i).aestronglyMeasurable.enorm)) hfinite
  filter_upwards [hae] with E hE
  exact tsum_enorm_ne_top_iff_summable_norm.mp hE.ne

/-- The literal pointwise sum is signed-integrable under the actual variation. -/
theorem signedIntegrable_tsum_of_summable_integral_norm
    (hi : ∀ i, ν.Integrable (F i))
    (hs : Summable (fun i => ∫ E, ‖F i E‖ ∂ν.variation)) :
    ν.Integrable (fun E => ∑' i, F i E) := by
  have hae := ae_summable_norm_of_summable_variation_integral_norm hi hs
  refine ⟨?_, ?_⟩
  · apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
      (fun s => s.aestronglyMeasurable_fun_sum (fun i _ => (hi i).aestronglyMeasurable))
    filter_upwards [hae] with E hE using hE.of_norm.hasSum
  · rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ E, ‖∑' i, F i E‖ₑ ∂ν.variation) ≤ ∫⁻ E, ∑' i, ‖F i E‖ₑ ∂ν.variation :=
        lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
      _ = ∑' i, ∫⁻ E, ‖F i E‖ₑ ∂ν.variation :=
        lintegral_tsum (fun i => (hi i).aestronglyMeasurable.enorm)
      _ < ∞ := (tsum_lintegral_enorm_variation_ne_top hi hs).lt_top

/-- Countable signed integration commutes with a series whose actual variation
norm integrals are summable. -/
theorem signedIntegral_tsum_of_summable_integral_norm
    (hi : ∀ i, ν.Integrable (F i))
    (hs : Summable (fun i => ∫ E, ‖F i E‖ ∂ν.variation)) :
    (∫ᵛ E, (∑' i, F i E) ∂<•ν) = ∑' i, ∫ᵛ E, F i E ∂<•ν :=
  VectorMeasure.integral_tsum (fun i => (hi i).aestronglyMeasurable)
    (tsum_lintegral_enorm_variation_ne_top hi hs)

/-- The exchanged signed-integral series has a genuine ordinary sum. -/
theorem hasSum_signedIntegral_of_summable_integral_norm
    (hi : ∀ i, ν.Integrable (F i))
    (hs : Summable (fun i => ∫ E, ‖F i E‖ ∂ν.variation)) :
    HasSum (fun i => ∫ᵛ E, F i E ∂<•ν) (∫ᵛ E, (∑' i, F i E) ∂<•ν) := by
  rw [signedIntegral_tsum_of_summable_integral_norm hi hs]
  apply (hs.of_norm_bounded ?_).hasSum
  intro i
  simpa only [ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.opNorm_lsmul,
    one_mul] using
    (VectorMeasure.norm_integral_le_integral_norm
      (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip) (μ := ν) (f := F i))

end Series

end GapFamily.Analytic
