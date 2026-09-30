import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Ordinary integrability and almost-everywhere absolute convergence for a countable
series of complex functions whose actual norm integrals are summable.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open MeasureTheory Filter
open scoped ENNReal Topology

variable {α ι : Type*} [MeasurableSpace α] [Countable ι]
  {μ : Measure α} {f : ι → α → ℂ}

omit [Countable ι] in
private theorem tsum_lintegral_enorm_ne_top_of_summable_integral_norm
    (hfi : ∀ i, Integrable (f i) μ)
    (hsum : Summable (fun i => ∫ a, ‖f i a‖ ∂μ)) :
    (∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ) ≠ ∞ := by
  have h (i : ι) : ∫⁻ a, ‖f i a‖ₑ ∂μ = ‖∫ a, ‖f i a‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hfi i).norm, ENNReal.coe_nnreal_eq,
      coe_nnnorm, Real.norm_of_nonneg
        (integral_nonneg (fun a => norm_nonneg (f i a)))]
    simp only [coe_nnnorm]
  rw [funext h]
  exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hsum.abs)

/-- Summable ordinary norm integrals imply almost-everywhere absolute convergence. -/
theorem ae_summable_norm_of_summable_integral_norm
    (hfi : ∀ i, Integrable (f i) μ)
    (hsum : Summable (fun i => ∫ a, ‖f i a‖ ∂μ)) :
    ∀ᵐ a ∂μ, Summable (fun i => ‖f i a‖) := by
  have hfinite := tsum_lintegral_enorm_ne_top_of_summable_integral_norm hfi hsum
  rw [← lintegral_tsum (fun i => (hfi i).aestronglyMeasurable.enorm)] at hfinite
  have hae := ae_lt_top'
    (AEMeasurable.tsum (fun i => (hfi i).aestronglyMeasurable.enorm)) hfinite
  filter_upwards [hae] with a ha
  exact tsum_enorm_ne_top_iff_summable_norm.mp ha.ne

/-- The literal pointwise tsum is an ordinary integrable function. -/
theorem integrable_tsum_of_summable_integral_norm
    (hfi : ∀ i, Integrable (f i) μ)
    (hsum : Summable (fun i => ∫ a, ‖f i a‖ ∂μ)) :
    Integrable (fun a => ∑' i, f i a) μ := by
  have hae := ae_summable_norm_of_summable_integral_norm hfi hsum
  refine ⟨?_, ?_⟩
  · apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
      (fun s => s.aestronglyMeasurable_fun_sum (fun i _ => (hfi i).aestronglyMeasurable))
    filter_upwards [hae] with a ha using ha.of_norm.hasSum
  · rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ a, ‖∑' i, f i a‖ₑ ∂μ) ≤ ∫⁻ a, ∑' i, ‖f i a‖ₑ ∂μ :=
        lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
      _ = ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ :=
        lintegral_tsum (fun i => (hfi i).aestronglyMeasurable.enorm)
      _ < ∞ := (tsum_lintegral_enorm_ne_top_of_summable_integral_norm hfi hsum).lt_top

end GapFamily.Analytic.SpatialPoint
