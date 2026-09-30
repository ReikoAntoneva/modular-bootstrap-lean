import GapFamily.Analytic.Foundation.AnalyticDominatedIntegral
import GapFamily.Analytic.Foundation.SignedMomentIntegral

/-!
Dominated norm analyticity of the actual Banach-valued signed integral.
The signed integral is identified with its Jordan difference only after
establishing variation integrability on the parameter neighborhood.
-/

noncomputable section
namespace GapFamily.Analytic.DominatedAnalytic
open MeasureTheory Filter Set Metric
open scoped Topology

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedSpace ℂ B] [CompleteSpace B]

/-- A common integrable bound and almost-everywhere analytic Banach-valued
slices give norm analyticity of the ordinary signed integral. -/
theorem analyticAt_signedIntegral_of_dominated
    {ν : SignedMeasure ℝ} {F : ℂ → ℝ → B} {z₀ : ℂ} {r : ℝ}
    {bound : ℝ → ℝ} (hr : 0 < r)
    (hmeas : ∀ z ∈ ball z₀ r, AEStronglyMeasurable (F z) ν.variation)
    (hanalytic : ∀ᵐ E ∂ν.variation,
      AnalyticOnNhd ℂ (fun z => F z E) (ball z₀ r))
    (hbound : ∀ᵐ E ∂ν.variation, ∀ z ∈ ball z₀ r, ‖F z E‖ ≤ bound E)
    (hint : Integrable bound ν.variation) :
    AnalyticAt ℂ (fun z => ∫ᵛ E, F z E ∂<•ν) z₀ := by
  have hp : ν.toJordanDecomposition.posPart ≤ ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation, SignedMeasure.totalVariation]
    exact Measure.le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation, SignedMeasure.totalVariation]
    exact Measure.le_add_left le_rfl
  have hpos := analyticAt_integral_of_dominated hr
    (fun z hz => (hmeas z hz).mono_measure hp)
    (hanalytic.filter_mono (ae_mono hp))
    (hbound.filter_mono (ae_mono hp)) (hint.mono_measure hp)
  have hneg := analyticAt_integral_of_dominated hr
    (fun z hz => (hmeas z hz).mono_measure hn)
    (hanalytic.filter_mono (ae_mono hn))
    (hbound.filter_mono (ae_mono hn)) (hint.mono_measure hn)
  apply (hpos.sub hneg).congr
  filter_upwards [ball_mem_nhds z₀ hr] with z hz
  exact (signedIntegral_eq_jordan
    (hint.mono' (hmeas z hz) (hbound.mono (fun E hE => hE z hz)))).symm

end GapFamily.Analytic.DominatedAnalytic
