import GapFamily.Analytic.Foundation.UpperWeightedPoissonJet
import GapFamily.Analytic.Elliptic.LocalPoissonProjection
import GapFamily.Analytic.Foundation.AnalyticClosedSubspace
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
namespace GapFamily.Analytic.UpperWeightedJet
open Set Filter MeasureTheory ModularGradient UpperHalfPlane CuspSchurLocal
open UpperSource LocalPoisson
open scoped ContDiff Topology

/-- Physical local weak equations continue on a common operator-norm disk. -/
theorem exists_ball_jet_mem_of_physical (U : Set ℂ)
    (J : ℂ → ModularHilbert →L[ℂ] Jet) (hJ : AnalyticAt ℂ J 0)
    (hphysical : ∃ ε : ℝ, 0 < ε ∧ ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re →
      ∀ f : ModularHilbert, J κ f ∈ jetSubmodule U) :
    ∃ r : ℝ, 0 < r ∧ AnalyticOnNhd ℂ J (Metric.ball 0 r) ∧
      ∀ κ : ℂ, ‖κ‖ < r → ∀ f : ModularHilbert, J κ f ∈ jetSubmodule U := by
  obtain ⟨ε, hε, hphysical⟩ := hphysical
  obtain ⟨rJ, hrJ, hJball⟩ := hJ.exists_ball_analyticOnNhd
  let r := min ε rJ
  have hr : 0 < r := lt_min hε hrJ
  have hrε : r ≤ ε := min_le_left _ _
  have hrrJ : r ≤ rJ := min_le_right _ _
  have hJr : AnalyticOnNhd ℂ J (Metric.ball (0 : ℂ) r) :=
    hJball.mono (Metric.ball_subset_ball hrrJ)
  let κ₀ : ℂ := ((r / 2 : ℝ) : ℂ)
  have hn₀ : ‖κ₀‖ < r := by
    dsimp [κ₀]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    linarith
  have hκ₀ : κ₀ ∈ Metric.ball (0 : ℂ) r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hn₀
  have hre₀ : 0 < κ₀.re := half_pos hr
  have hnearN : ∀ᶠ κ : ℂ in 𝓝 κ₀, ‖κ‖ < ε :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (hn₀.trans_le hrε)
  have hnearR : ∀ᶠ κ : ℂ in 𝓝 κ₀, 0 < κ.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre₀
  refine ⟨r, hr, hJr, ?_⟩
  intro κ hκ f
  have hJf : AnalyticOnNhd ℂ (fun z => J z f) (Metric.ball (0 : ℂ) r) :=
    fun z hz => ((ContinuousLinearMap.apply ℂ Jet f).analyticAt _).comp (hJr z hz)
  have hnear : ∀ᶠ z in 𝓝 κ₀, J z f ∈ jetSubmodule U := by
    filter_upwards [hnearN, hnearR] with z hn hp
    exact hphysical z hn hp f
  exact analyticOnNhd_mem_closedSubmodule_of_eventually_mem (jetSubmodule U)
    (isClosed_jetSubmodule U) hJf Metric.isPreconnected_ball hκ₀ hnear κ
    (by simpa only [Metric.mem_ball, dist_zero_right] using hκ)

/-- Actual weighted upper-chart jets, analytic through threshold with all four
original coordinates retained on one disk for every source. -/
theorem exists_analytic_continuedJet
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    {α : ℝ} (hα : 0 < α) :
    ∃ (J : ℂ → ModularHilbert →L[ℂ] Jet)
      (Q : ℂ → ModularHilbert →L[ℂ] JetSpace U) (r : ℝ), 0 < r ∧
      AnalyticOnNhd ℂ J (Metric.ball 0 r) ∧ AnalyticOnNhd ℂ Q (Metric.ball 0 r) ∧
      ∀ κ : ℂ, ‖κ‖ < r →
        (jetSubmodule U).subtypeL.comp (Q κ) = J κ ∧
        (0 < κ.re → ∀ f : ModularHilbert,
          ∃ hu : CuspSchur.actualSchurResolvent (parameter κ)
              (cuspWeightedInput α hα.le f) ∈ laplacian.domain,
            J κ f = actualJet χ hχ hc hs
              ⟨CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f), hu⟩) := by
  obtain ⟨J, hJ, ε, hε, hphysical⟩ :=
    exists_analytic_physicalJet_mem χ hχ hc hs U hU hχU hα
  obtain ⟨r, hr, hJr, hmem⟩ := exists_ball_jet_mem_of_physical U J hJ
    ⟨ε, hε, fun κ hn hp f => (hphysical κ hn hp f).1⟩
  let δ := min ε r
  have hδ : 0 < δ := lt_min hε hr
  have hδr : δ ≤ r := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  refine ⟨J, fun κ => jetOperator ModularHilbert U (J κ), δ, hδ,
    hJr.mono (Metric.ball_subset_ball hδr),
    jetOperator_analyticOnNhd ModularHilbert U _ (hJr.mono (Metric.ball_subset_ball hδr)), ?_⟩
  intro κ hn
  refine ⟨jetOperator_subtype_of_mem ModularHilbert U (J κ) (hmem κ (hn.trans_le hδr)), ?_⟩
  intro hp f
  exact (hphysical κ (hn.trans_le hδε) hp f).2

end GapFamily.Analytic.UpperWeightedJet
