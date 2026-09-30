import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorDensity
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorTrace
import Mathlib.MeasureTheory.Integral.Prod

/-! Ordinary Fubini pairing for the actual collar Green operator. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Filter

/-- Every continuous test pairing against the actual continuous response is integrable. -/
theorem cuspGreenCollar_testPairing_integrable (a b : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) (g : C(CuspGreenCollar a b, ℂ)) :
    Integrable (fun t => cuspGreenCollarOperator a b κ f t * g t)
      (cuspGreenCollarMeasure a b) :=
  (cuspGreenCollarOperator a b κ f * g).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The double source/test integrand is ordinarily integrable before Fubini is used. -/
theorem cuspGreenCollar_doublePairing_integrable (a b : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) (g : C(CuspGreenCollar a b, ℂ)) :
    Integrable (fun p : CuspGreenCollar a b × CuspGreenCollar a b =>
      (cuspGreen a p.1 p.2 κ * g p.1) * f p.2)
      ((cuspGreenCollarMeasure a b).prod (cuspGreenCollarMeasure a b)) := by
  let H : C(CuspGreenCollar a b × CuspGreenCollar a b, ℂ) :=
    cuspGreenCollarKernel a b κ * g.comp ⟨Prod.fst, continuous_fst⟩
  exact ((cuspGreenCollarSource_integrable a b f).comp_snd
    (cuspGreenCollarMeasure a b)).bdd_mul H.continuous.aestronglyMeasurable
      (Eventually.of_forall H.norm_coe_le_norm)

/-- Symmetry of the genuine kernel passes to its ordinary bilinear source pairing. -/
theorem cuspGreenCollar_pairing (a b : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) (g : C(CuspGreenCollar a b, ℂ)) :
    (∫ t : CuspGreenCollar a b, cuspGreenCollarOperator a b κ f t * g t
      ∂cuspGreenCollarMeasure a b) =
      ∫ u : CuspGreenCollar a b,
        cuspGreenCollarOperator a b κ
          (ContinuousMap.toLp 2 (cuspGreenCollarMeasure a b) ℂ g) u * f u
        ∂cuspGreenCollarMeasure a b := by
  calc
    _ = ∫ t : CuspGreenCollar a b, ∫ u : CuspGreenCollar a b,
        (cuspGreen a t u κ * g t) * f u
        ∂cuspGreenCollarMeasure a b ∂cuspGreenCollarMeasure a b := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [cuspGreenCollarOperator_apply, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with u
      ring
    _ = ∫ u : CuspGreenCollar a b, ∫ t : CuspGreenCollar a b,
        (cuspGreen a t u κ * g t) * f u
        ∂cuspGreenCollarMeasure a b ∂cuspGreenCollarMeasure a b :=
      integral_integral_swap (cuspGreenCollar_doublePairing_integrable a b κ f g)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_mul_const, cuspGreenCollarOperator_apply_continuous]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [cuspGreen_symm a t u κ]

end GapFamily.Analytic
