import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinatePairing
import GapFamily.Analytic.Cusp.Green.CuspGreenWeakPairing

/-!
# The literal physical Green test equation

Every actual collar L² source satisfies the physical spectral test equation,
with both integrals genuinely convergent and no source smoothness premise.
-/

noncomputable section

namespace GapFamily.Analytic
open Set MeasureTheory
open scoped ContDiff

/-- Literal physical Green response for every collar L² source obeys the
spectral test equation, with ordinary convergent physical and source integrals. -/
theorem cuspGreenCollarResponse_physical_test (T : ℝ) (hT : 0 ≤ T) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) {b : ℝ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    IntegrableOn (fun y =>
      (inner ℂ (cuspProfileSecondOrder b y) (cuspLift (cuspGreenCollarResponse 0 T κ f) y) -
        (1/4 - κ^2) * inner ℂ (b y) (cuspLift (cuspGreenCollarResponse 0 T κ f) y)) /
        (y : ℂ)^2) (Ioi 1) ∧
    Integrable (fun u : CuspGreenCollar 0 T => inner ℂ (cuspLogCoordinate b u) (f u))
      (cuspGreenCollarMeasure 0 T) ∧
    (∫ y in Ioi (1 : ℝ),
      (inner ℂ (cuspProfileSecondOrder b y) (cuspLift (cuspGreenCollarResponse 0 T κ f) y) -
        (1/4 - κ^2) * inner ℂ (b y) (cuspLift (cuspGreenCollarResponse 0 T κ f) y)) /
        (y : ℂ)^2) =
      ∫ u : CuspGreenCollar 0 T, inner ℂ (cuspLogCoordinate b u) (f u)
        ∂cuspGreenCollarMeasure 0 T := by
  have h := cuspGreenCollarResponse_test_first_halfline 0 T hT κ f
    ((contDiff_cuspLogCoordinate hb).of_le (by simp))
    (hasCompactSupport_cuspLogCoordinate hc hs) (tsupport_cuspLogCoordinate_subset hs)
  refine ⟨(integrableOn_cuspLogCoordinate_spectral_inner_iff hb _ κ).mpr h.1, h.2.1, ?_⟩
  rw [integral_cuspLogCoordinate_spectral_inner hb]
  exact h.2.2

/-- The actual collar source has the same literal Green response at every real point. -/
theorem cuspGreenCollarResponse_source_eq_solution (T : ℝ) (hT : 0 ≤ T) (κ : ℂ)
    (f : ℝ → ℂ) (hf : Continuous f) (hfT : ∀ u, T < u → f u = 0) (t : ℝ) :
    cuspGreenCollarResponse 0 T κ (cuspGreenCollarSource 0 T f hf) t =
      cuspGreenSolution 0 κ f t := by
  unfold cuspGreenCollarResponse
  calc
    _ = ∫ u : CuspGreenCollar 0 T,
      cuspGreen 0 t u κ * f u ∂cuspGreenCollarMeasure 0 T := by
      apply integral_congr_ae
      filter_upwards [cuspGreenCollarSource_coeFn 0 T f hf] with u hu
      rw [hu]
    _ = ∫ u : ℝ in Icc 0 T, cuspGreen 0 t u κ * f u :=
      integral_subtype_comap measurableSet_Icc (fun u : ℝ => cuspGreen 0 t u κ * f u)
    _ = _ := by rw [cuspGreenSolution_eq_interval 0 T t hT κ hfT,
      intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

end GapFamily.Analytic
