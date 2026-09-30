import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurEvaluation

noncomputable section
namespace GapFamily.Analytic.CuspSchurCoherence
open Set Filter ModularGradient CuspSchurLocal
open scoped Topology ContDiff

/-- A physical half-neighborhood determines an analytic germ uniquely. -/
theorem analyticAt_eventuallyEq_of_physical
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F G : ℂ → E} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (hphysical : ∃ ε : ℝ, 0 < ε ∧ ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re → F κ = G κ) :
    F =ᶠ[𝓝 (0 : ℂ)] G := by
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
  have hnear : F =ᶠ[𝓝 κ₀] G := by
    filter_upwards [hnearNorm, hnearRe] with κ hn hp
    exact hphysical κ hn hp
  have heq := hFr.eqOn_of_preconnected_of_eventuallyEq hGr Metric.isPreconnected_ball hκ₀ hnear
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with κ hκ
  exact heq hκ

/-- Actual smooth cutoffs give the same local operator germ. -/
theorem continuedLocalEvaluation_eventuallyEq
    (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    (χ₁ : ℂ → ℝ) (hχ₁ : ContDiff ℝ ∞ χ₁) (hc₁ : HasCompactSupport χ₁)
    (hs₁ : tsupport χ₁ ⊆ modularInterior) (hK₁ : EqOn χ₁ (fun _ => 1) K)
    (χ₂ : ℂ → ℝ) (hχ₂ : ContDiff ℝ ∞ χ₂) (hc₂ : HasCompactSupport χ₂)
    (hs₂ : tsupport χ₂ ⊆ modularInterior) (hK₂ : EqOn χ₂ (fun _ => 1) K)
    {L₁ L₂ T : ℝ} (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hT : 0 ≤ T)
    (hH₁ : tsupport χ₁ ⊆ {z : ℂ | z.im ≤ Real.exp L₁})
    (hH₂ : tsupport χ₂ ⊆ {z : ℂ | z.im ≤ Real.exp L₂}) :
    continuedLocalEvaluation K hKU hreg χ₁ hχ₁ hc₁ L₁ T =ᶠ[𝓝 (0 : ℂ)]
      continuedLocalEvaluation K hKU hreg χ₂ hχ₂ hc₂ L₂ T := by
  apply analyticAt_eventuallyEq_of_physical
    (continuedLocalEvaluation_analyticAt_zero K hKU hreg χ₁ hχ₁ hc₁ L₁ T)
    (continuedLocalEvaluation_analyticAt_zero K hKU hreg χ₂ hχ₂ hc₂ L₂ T)
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_radius_continuedLocalEvaluation_eq_physical
    K hKU hreg χ₁ hχ₁ hc₁ hs₁ hK₁ hL₁ hT hH₁
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_radius_continuedLocalEvaluation_eq_physical
    K hKU hreg χ₂ hχ₂ hc₂ hs₂ hK₂ hL₂ hT hH₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro κ hn hp
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨hu₁, he₁⟩ := h₁ κ (hn.trans_le (min_le_left _ _)) hp f
  obtain ⟨hu₂, he₂⟩ := h₂ κ (hn.trans_le (min_le_right _ _)) hp f
  exact he₁.trans he₂.symm

/-- In particular the actual threshold evaluation has no cutoff dependence. -/
theorem continuedLocalEvaluation_zero_eq
    (K : Set ℂ) [CompactSpace K]
    (hKU : K ⊆ modularInterior) (hreg : K ⊆ closure (interior K))
    (χ₁ : ℂ → ℝ) (hχ₁ : ContDiff ℝ ∞ χ₁) (hc₁ : HasCompactSupport χ₁)
    (hs₁ : tsupport χ₁ ⊆ modularInterior) (hK₁ : EqOn χ₁ (fun _ => 1) K)
    (χ₂ : ℂ → ℝ) (hχ₂ : ContDiff ℝ ∞ χ₂) (hc₂ : HasCompactSupport χ₂)
    (hs₂ : tsupport χ₂ ⊆ modularInterior) (hK₂ : EqOn χ₂ (fun _ => 1) K)
    {L₁ L₂ T : ℝ} (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hT : 0 ≤ T)
    (hH₁ : tsupport χ₁ ⊆ {z : ℂ | z.im ≤ Real.exp L₁})
    (hH₂ : tsupport χ₂ ⊆ {z : ℂ | z.im ≤ Real.exp L₂}) :
    continuedLocalEvaluation K hKU hreg χ₁ hχ₁ hc₁ L₁ T 0 =
      continuedLocalEvaluation K hKU hreg χ₂ hχ₂ hc₂ L₂ T 0 :=
  (continuedLocalEvaluation_eventuallyEq K hKU hreg χ₁ hχ₁ hc₁ hs₁ hK₁
    χ₂ hχ₂ hc₂ hs₂ hK₂ hL₁ hL₂ hT hH₁ hH₂).self_of_nhds

end GapFamily.Analytic.CuspSchurCoherence
