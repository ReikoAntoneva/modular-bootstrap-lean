import GapFamily.Analytic.Foundation.AnalyticClosedSubspace
import GapFamily.Analytic.Modular.ModularLaplacian
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Uniform continuation into the actual modular Laplacian graph

One parameter ball works for every Hilbert source. The physical graph equation
on its positive-real side supplies an ambient neighborhood of a positive-real
interior seed. The analytic identity principle then continues that equation
through zero in the actual closed operator graph.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set Filter
open scoped Topology

/-- Two actual operator-norm analytic families satisfying the physical graph
condition acquire a common analytic neighborhood on which every source pair
belongs to the true modular Laplacian graph. The radius is independent of the
source. The physical condition remains an ordinary explicit hypothesis. -/
theorem exists_ball_laplacian_graph_of_physical
    (F G : ℂ → (ModularHilbert →L[ℂ] ModularHilbert))
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (hphysical : ∃ ε : ℝ, 0 < ε ∧ ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re →
      ∀ f : ModularHilbert, (F κ f, G κ f) ∈ laplacian.graph) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) r) ∧
      AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) r) ∧
      ∀ κ : ℂ, ‖κ‖ < r →
        ∀ f : ModularHilbert, (F κ f, G κ f) ∈ laplacian.graph := by
  obtain ⟨ε, hε, hphysical⟩ := hphysical
  obtain ⟨rF, hrF, hFball⟩ := hF.exists_ball_analyticOnNhd
  obtain ⟨rG, hrG, hGball⟩ := hG.exists_ball_analyticOnNhd
  let r := min ε (min rF rG)
  have hr : 0 < r := lt_min hε (lt_min hrF hrG)
  have hrε : r ≤ ε := min_le_left _ _
  have hrF' : r ≤ rF := (min_le_right _ _).trans (min_le_left _ _)
  have hrG' : r ≤ rG := (min_le_right _ _).trans (min_le_right _ _)
  have hFr : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) r) :=
    hFball.mono (Metric.ball_subset_ball hrF')
  have hGr : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) r) :=
    hGball.mono (Metric.ball_subset_ball hrG')
  let κ₀ : ℂ := ((r / 2 : ℝ) : ℂ)
  have hκ₀norm : ‖κ₀‖ < r := by
    dsimp [κ₀]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    linarith
  have hκ₀ : κ₀ ∈ Metric.ball (0 : ℂ) r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hκ₀norm
  have hκ₀re : 0 < κ₀.re := by
    change 0 < r / 2
    exact half_pos hr
  have hnearNorm : ∀ᶠ κ : ℂ in 𝓝 κ₀, ‖κ‖ < ε :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (hκ₀norm.trans_le hrε)
  have hnearRe : ∀ᶠ κ : ℂ in 𝓝 κ₀, 0 < κ.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hκ₀re
  have hnear : ∀ᶠ κ : ℂ in 𝓝 κ₀,
      ∀ f : ModularHilbert, (F κ f, G κ f) ∈ laplacian.graph := by
    filter_upwards [hnearNorm, hnearRe] with κ hnorm hre
    exact hphysical κ hnorm hre
  refine ⟨r, hr, hFr, hGr, ?_⟩
  intro κ hκ f
  have hFf : AnalyticOnNhd ℂ (fun k => F k f) (Metric.ball (0 : ℂ) r) :=
    fun k hk => ((ContinuousLinearMap.apply ℂ ModularHilbert f).analyticAt _).comp (hFr k hk)
  have hGf : AnalyticOnNhd ℂ (fun k => G k f) (Metric.ball (0 : ℂ) r) :=
    fun k hk => ((ContinuousLinearMap.apply ℂ ModularHilbert f).analyticAt _).comp (hGr k hk)
  exact analyticOnNhd_mem_graph_of_eventually_mem laplacian laplacian_isClosed
    hFf hGf Metric.isPreconnected_ball hκ₀ (hnear.mono fun k hk => hk f) κ
    (by simpa only [Metric.mem_ball, dist_zero_right] using hκ)

end GapFamily.Analytic.ModularGradient
