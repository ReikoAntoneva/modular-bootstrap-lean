import GapFamily.Analytic.Elliptic.ContinuousMollifierLimit
import GapFamily.Analytic.Elliptic.ContinuousWeakDerivativeMollifier
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticMollifier
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory Metric ContinuousLinearMap ModularGradient
open scoped ContDiff Convolution Topology

/-- A continuous field with a continuous literal weak gradient is genuinely
Fréchet differentiable at every point of its open domain. No regularity or
integrability of arbitrary values outside that domain is assumed. -/
theorem hasFDerivAt_of_continuousOn_weak_gradient
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} {G : ℂ → (ℂ →L[ℝ] ℂ)}
    (hf : ContinuousOn f U) (hG : ContinuousOn G U)
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∀ v : ℂ,
      (∫ t : ℂ, fderiv ℝ ψ t v • f t) = -(∫ t : ℂ, ψ t • G t v))
    {x : ℂ} (hx : x ∈ U) : HasFDerivAt f (G x) x := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU x hx
  let r : ℝ := R / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let K := closedBall x (3 * r)
  have hKU : K ⊆ U := by
    intro y hy
    apply hRU
    have hy' : dist y x ≤ 3 * r := hy
    change dist y x < R
    dsimp [r] at hy'
    linarith
  have hsmall : ball x (2 * r) ⊆ K := by
    intro y hy
    have hy' : dist y x < 2 * r := hy
    change dist y x ≤ 3 * r
    linarith
  have hballK : ball x r ⊆ K := by
    intro y hy
    have hy' : dist y x < r := hy
    change dist y x ≤ 3 * r
    linarith
  let fK : ℂ → ℂ := K.indicator f
  let GK : ℂ → (ℂ →L[ℝ] ℂ) := K.indicator G
  have hfK : Integrable fK volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      ((hf.mono hKU).integrableOn_compact (isCompact_closedBall _ _))
  have hGK : Integrable GK volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      ((hG.mono hKU).integrableOn_compact (isCompact_closedBall _ _))
  have hcf : ContinuousOn fK (ball x r) := by
    apply (hf.mono (hballK.trans hKU)).congr
    intro y hy
    simp only [fK, indicator_of_mem (hballK hy)]
  have hcG : ContinuousOn GK (ball x r) := by
    apply (hG.mono (hballK.trans hKU)).congr
    intro y hy
    simp only [GK, indicator_of_mem (hballK hy)]
  have hwK : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball x (2 * r) → ∀ v : ℂ,
      (∫ t : ℂ, fderiv ℝ ψ t v • fK t) = -(∫ t : ℂ, ψ t • GK t v) := by
    intro ψ hψ hc hs v
    have hsK := hs.trans hsmall
    have hleft : (∫ t : ℂ, fderiv ℝ ψ t v • fK t) =
        ∫ t : ℂ, fderiv ℝ ψ t v • f t := by
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ K
      · simp only [fK, indicator_of_mem ht]
      · have hd : fderiv ℝ ψ t = 0 := fderiv_of_notMem_tsupport ℝ (fun hh => ht (hsK hh))
        simp only [hd, zero_apply, zero_smul]
    have hright : (∫ t : ℂ, ψ t • GK t v) = ∫ t : ℂ, ψ t • G t v := by
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ K
      · simp only [GK, indicator_of_mem ht]
      · have hz : ψ t = 0 := image_eq_zero_of_notMem_tsupport (fun hh => ht (hsK hh))
        simp only [hz, zero_smul]
    rw [hleft, hright]
    exact hweak ψ hψ hc (hsK.trans hKU) v
  let φ := ellipticShrinkingBump r hr
  have hφ := ellipticShrinkingBump_tendsto r hr
  have hderiv (n : ℕ) (y : ℂ) (hy : y ∈ ball x r) :
      HasFDerivAt ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] fK)
        (((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] GK) y) y :=
    hasFDerivAt_convolution_of_weak_gradient hfK.locallyIntegrable hGK.locallyIntegrable hwK
      (φ n).contDiff_normed (φ n).hasCompactSupport_normed y
      (normed_reflected_kernel_tsupport_subset_ball x hr (φ n)
        (ellipticShrinkingBump_rOut_lt r hr n) hy)
  have hlimG := normed_bump_convolution_tendstoLocallyUniformlyOn hφ
    hGK.aestronglyMeasurable isOpen_ball hcG
  have hlimf (y : ℂ) (hy : y ∈ ball x r) :=
    normed_bump_convolution_tendsto_of_continuousOn hφ
      hfK.aestronglyMeasurable isOpen_ball hcf hy
  have hdf : HasFDerivAt fK (GK x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_ball hlimG hderiv hlimf (mem_ball_self hr)
  have heq : f =ᶠ[𝓝 x] fK := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with y hy
    simp only [fK, indicator_of_mem (hballK hy)]
  have hxK : x ∈ K := mem_closedBall_self (by positivity)
  simpa only [GK, indicator_of_mem hxK] using hdf.congr_of_eventuallyEq heq

/-- The actual derivative equals the specified continuous weak gradient on the open set. -/
theorem fderiv_eq_of_continuousOn_weak_gradient
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} {G : ℂ → (ℂ →L[ℝ] ℂ)}
    (hf : ContinuousOn f U) (hG : ContinuousOn G U)
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∀ v : ℂ,
      (∫ t : ℂ, fderiv ℝ ψ t v • f t) = -(∫ t : ℂ, ψ t • G t v)) :
    EqOn (fderiv ℝ f) G U :=
  fun _ hx => (hasFDerivAt_of_continuousOn_weak_gradient hU hf hG hweak hx).fderiv

/-- Continuous weak gradients give actual C¹ regularity, with no smoothing-sequence premise. -/
theorem contDiffOn_one_of_continuousOn_weak_gradient
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} {G : ℂ → (ℂ →L[ℝ] ℂ)}
    (hf : ContinuousOn f U) (hG : ContinuousOn G U)
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∀ v : ℂ,
      (∫ t : ℂ, fderiv ℝ ψ t v • f t) = -(∫ t : ℂ, ψ t • G t v)) :
    ContDiffOn ℝ 1 f U := by
  rw [show (1 : ℕ∞ω) = 0 + 1 by rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun x hx => (hasFDerivAt_of_continuousOn_weak_gradient hU hf hG hweak hx).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  apply hG.congr
  intro x hx
  exact fderiv_eq_of_continuousOn_weak_gradient hU hf hG hweak hx

end GapFamily.Analytic
