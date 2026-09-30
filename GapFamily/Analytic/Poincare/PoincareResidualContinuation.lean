import GapFamily.Analytic.Foundation.AnalyticBallGlue
import GapFamily.Analytic.Poincare.PoincarePhysicalResponse
import GapFamily.Analytic.Poincare.Continuation.PoincareCommonRegionEvaluation

noncomputable section
namespace GapFamily.Analytic.PoincareResidualContinuation
open Set Filter MeasureTheory ModularGradient CuspFourierCutoff CuspSchurLocal UpperHalfPlane
open PoincarePhysicalResponse
open scoped ContDiff Topology

/-- The fixed physical graph response recovers the original full Poincaré
series after the actual high-cusp lift is restored. -/
theorem physicalResidualResponse_add_highCusp_eq_series
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (J : ℤ)
    {κ : ℂ} (hκ : (3 / 2 : ℝ) < κ.re) (z : K) :
    physicalResidualResponse χ hχ hc hs U hU hχU K hKU J κ z +
      PoincareHighCusp.continuedHighCusp J κ z =
        complexPoincareSeries 0 J (exponent κ) (ofComplex z) := by
  obtain ⟨hu, he⟩ := PoincareComplement.exists_actualSchur_evaluation_add_highCusp_eq_series
    J hκ χ hχ hc hs U hU hχU K hKU
  have hp : 0 < κ.re := by linarith
  have hh : κ ≠ (1 / 2 : ℂ) := by intro h; rw [h] at hκ; norm_num at hκ
  rw [physicalResidualResponse_eq_gradientLift χ hχ hc hs U hU hχU K hKU J hp hh hu]
  exact he z

/-- The actual residual response has one norm-analytic continuation from the
whole physical region through threshold. Its disk and quadratic spin constant
are fixed before the spin, and the common-region reconstruction is literal. -/
theorem exists_continuedResidualResponse
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) :
    ∃ (G : ℤ → ℂ → C(K, ℂ)) (r C : ℝ),
      0 < r ∧ r ≤ 1 / 8 ∧ 0 < C ∧
      (∀ J : ℤ, AnalyticOnNhd ℂ (G J)
        (Metric.ball 0 r ∪ {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)})) ∧
      (∀ (J : ℤ) (κ : ℂ), 0 < κ.re → κ ≠ (1 / 2 : ℂ) →
        G J κ = physicalResidualResponse χ hχ hc hs U hU hχU K hKU J κ) ∧
      (∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ r → ‖G J κ‖ ≤ C * (1 + (J : ℝ) ^ 2)) ∧
      ∀ (J : ℤ) (κ : ℂ), (3 / 2 : ℝ) < κ.re → ∀ z : K,
        G J κ z + PoincareHighCusp.continuedHighCusp J κ z =
          complexPoincareSeries 0 J (exponent κ) (ofComplex z) := by
  obtain ⟨R, r₀, C, hr₀, hr₀8, hC, hR, hbound, hmatch⟩ :=
    exists_thresholdResidualResponse χ hχ hc hs U hU hχU K hKU
  let V : Set ℂ := {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  let A := physicalResidualResponse χ hχ hc hs U hU hχU K hKU
  let G (J : ℤ) := analyticBallGlue r₀ (R J) (A J)
  have hAB (J : ℤ) : EqOn (R J) (A J) (Metric.ball 0 r₀ ∩ V) := by
    intro κ hκ
    exact hmatch J κ (by simpa only [Metric.mem_ball, dist_zero_right] using hκ.1) hκ.2.1
  have hGA (J : ℤ) : EqOn (G J) (A J) V :=
    analyticBallGlue_eqOn_of_eqOn r₀ (R J) (A J) (hAB J)
  refine ⟨G, r₀ / 2, C, by positivity, by linarith, hC, ?_, ?_, ?_, ?_⟩
  · intro J
    have ha := analyticBallGlue_analyticOnNhd r₀ hV (hR J)
      (physicalResidualResponse_analyticOnNhd χ hχ hc hs U hU hχU K hKU J) (hAB J)
    exact ha.mono (union_subset_union (Metric.ball_subset_ball (by linarith : r₀ / 2 ≤ r₀)) Subset.rfl)
  · intro J κ hp hh
    exact hGA J ⟨hp, hh⟩
  · intro J κ hn
    have hn₀ : ‖κ‖ < r₀ := by linarith
    have he : G J κ = R J κ :=
      analyticBallGlue_eqOn_ball r₀ (R J) (A J)
        (by simpa only [Metric.mem_ball, dist_zero_right] using hn₀)
    rw [he]
    exact hbound J κ hn₀.le
  · intro J κ hκ z
    have hp : 0 < κ.re := by linarith
    have hh : κ ≠ (1 / 2 : ℂ) := by intro h; rw [h] at hκ; norm_num at hκ
    rw [hGA J ⟨hp, hh⟩]
    exact physicalResidualResponse_add_highCusp_eq_series χ hχ hc hs U hU hχU K hKU J hκ z

end GapFamily.Analytic.PoincareResidualContinuation
