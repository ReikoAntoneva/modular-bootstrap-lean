import GapFamily.Analytic.Poincare.Continuation.PoincareCompactContinuation
import GapFamily.Analytic.Poincare.Continuation.PoincareCompactSeriesAnalytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex

/-! The existing compact continuation agrees with the original sum throughout
its complete absolute-convergence region, by Banach-valued analytic uniqueness. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCompactContinuation
open Set Filter ModularGradient UpperHalfPlane CuspFourierCutoff
open PoincareConvergentAnalytic
open scoped Topology

/-- The same actual compact continuation, disk, and spin bound recover the
original sum on every parameter in its full convergence half-plane. -/
theorem exists_compactPoincareContinuation_full_convergence
    (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ (P : ℤ → ℂ → C(K, ℂ)) (r C : ℝ),
      0 < r ∧ r ≤ 1 / 8 ∧ 0 < C ∧
      (∀ J : ℤ, AnalyticOnNhd ℂ (P J)
        (Metric.ball 0 r ∪ {κ : ℂ | 0 < κ.re ∧ κ ≠ (1 / 2 : ℂ)})) ∧
      (∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ r → ‖P J κ‖ ≤ C * (1 + (J : ℝ) ^ 2)) ∧
      ∀ (J : ℤ) (κ : ℂ), (1 / 2 : ℝ) < κ.re → ∀ z : K,
        P J κ z = complexPoincareSeries 0 J (exponent κ) (ofComplex z) := by
  obtain ⟨P, r, C, hr, hr8, hC, hP, hbound, hcommon⟩ :=
    exists_compactPoincareContinuation K hKH
  refine ⟨P, r, C, hr, hr8, hC, hP, hbound, ?_⟩
  intro J κ hκ z
  let U : Set ℂ := {w : ℂ | (1 / 2 : ℝ) < w.re}
  have hPU : AnalyticOnNhd ℂ (P J) U := by
    intro w hw
    apply hP J w
    right
    refine ⟨by dsimp [U] at hw; linarith, ?_⟩
    intro he
    subst w
    norm_num [U] at hw
  have hQU : AnalyticOnNhd ℂ
      (fun w => compactSeries K hKH J (exponent w)) U :=
    fun _ hw => compactSeries_exponent_analyticAt K hKH J hw
  have hU : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  have hgerm : (P J) =ᶠ[𝓝 (2 : ℂ)]
      (fun w => compactSeries K hKH J (exponent w)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (3 / 2 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    apply ContinuousMap.ext
    intro x
    have hs : 1 < (exponent w).re := by norm_num [exponent, Complex.add_re]; linarith
    exact (hcommon J w hw x).trans (compactSeries_apply K hKH J hs x).symm
  have heq := (hPU.eqOn_of_preconnected_of_eventuallyEq hQU hU htwo hgerm) hκ
  rw [heq]
  apply compactSeries_apply K hKH J
  norm_num [exponent, Complex.add_re]
  linarith

end GapFamily.Analytic.PoincareCompactContinuation
