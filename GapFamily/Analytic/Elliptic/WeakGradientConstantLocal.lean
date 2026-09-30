import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Local constancy from zero weak gradient

The convolution derivative is the pinned Mathlib theorem. Reflection and
translation turn its kernel into an admissible ordinary weak-derivative test.
No differentiability of the locally integrable function is assumed.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory Filter Metric ContinuousLinearMap
open scoped ContDiff Convolution Topology

private def reflectTranslate (y : ℂ) : Homeomorph ℂ ℂ :=
  (Homeomorph.neg ℂ).trans (Homeomorph.addLeft y)

private theorem reflectTranslate_apply (y t : ℂ) : reflectTranslate y t = y - t := by
  simp [reflectTranslate, sub_eq_add_neg]

private theorem fderiv_reflected_test (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η)
    (y t v : ℂ) :
    fderiv ℝ (η ∘ reflectTranslate y) t v = - fderiv ℝ η (y - t) v := by
  have ht : HasFDerivAt (fun t : ℂ => y - t) (- ContinuousLinearMap.id ℝ ℂ) t := by
    simpa using! (hasFDerivAt_const y t).sub (hasFDerivAt_id t)
  have hcomp := ((hη.differentiable (by simp)).differentiableAt.hasFDerivAt).comp t ht
  have heq : η ∘ reflectTranslate y = fun t => η (y - t) := by
    funext t
    rw [Function.comp_apply, reflectTranslate_apply]
  rw [heq]
  simpa [Function.comp_def] using congrArg (fun A : ℂ →L[ℝ] ℝ => A v) hcomp.fderiv

/-- A globally locally integrable function with zero weak gradient against
tests in `V` has zero mollified derivative whenever the reflected kernel is
supported in `V`. The integrals in this auxiliary statement are global. -/
private theorem hasFDerivAt_zero_convolution_of_test_zero
    {g : ℂ → ℂ} (hg : LocallyIntegrable g volume) {V : Set ℂ}
    (hzero : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ V → ∀ v : ℂ, ∫ t, (fderiv ℝ ψ t v) • g t = 0)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (y : ℂ) (hs : tsupport (η ∘ reflectTranslate y) ⊆ V) :
    HasFDerivAt (η ⋆[lsmul ℝ ℝ, volume] g) (0 : ℂ →L[ℝ] ℂ) y := by
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (lsmul ℝ ℝ).flip
  have hd := hc.hasFDerivAt_convolution_right L hg (hη.of_le (by simp)) y
  have hψ : ContDiff ℝ ∞ (η ∘ reflectTranslate y) := by
    have heq : η ∘ reflectTranslate y = fun t => η (y - t) := by
      funext t
      rw [Function.comp_apply, reflectTranslate_apply]
    rw [heq]
    exact hη.comp (contDiff_const.sub contDiff_id)
  have hD : ((g ⋆[L.precompR ℂ, volume] fderiv ℝ η) y) = 0 := by
    ext v
    rw [convolution_precompR_apply L hg (hc.fderiv ℝ)
      (hη.continuous_fderiv (by simp))]
    have hz := hzero (η ∘ reflectTranslate y) hψ (hc.comp_homeomorph _) hs v
    have hneg : (∫ t, fderiv ℝ (η ∘ reflectTranslate y) t v • g t) =
        -(∫ t, fderiv ℝ η (y - t) v • g t) := by
      simp_rw [fderiv_reflected_test η hη y, neg_smul]
      rw [integral_neg]
    rw [hneg, neg_eq_zero] at hz
    simpa only [convolution_def, L, flip_apply, lsmul_apply, zero_apply] using hz
  rw [hD] at hd
  simpa only [L, convolution_flip] using hd

/-- Zero weak gradient on a doubled ball makes every smaller normalized
mollification constant on the original ball. -/
theorem normed_convolution_const_on_ball_of_test_zero
    {g : ℂ → ℂ} (hg : LocallyIntegrable g volume) (x : ℂ) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball x (2 * r) →
      ∀ v : ℂ, ∫ t, (fderiv ℝ ψ t v) • g t = 0)
    (φ : ContDiffBump (0 : ℂ)) (hφ : φ.rOut < r) :
    ∀ z ∈ ball x r, (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z =
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) x := by
  have hD : ∀ y ∈ ball x r,
      HasFDerivAt (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) (0 : ℂ →L[ℝ] ℂ) y := by
    intro y hy
    apply hasFDerivAt_zero_convolution_of_test_zero hg hzero
      (φ.normed volume) φ.contDiff_normed φ.hasCompactSupport_normed y
    rw [tsupport_comp_eq_preimage]
    intro t ht
    have hyt : dist t y ≤ φ.rOut := by
      have hm : reflectTranslate y t ∈ closedBall (0 : ℂ) φ.rOut := by
        simpa only [φ.tsupport_normed_eq, mem_preimage] using ht
      simpa only [mem_closedBall, reflectTranslate_apply, dist_zero_right,
        ← dist_eq_norm_sub, dist_comm y t] using hm
    have htx := dist_triangle t y x
    have hyx : dist y x < r := hy
    change dist t x < 2 * r
    linarith
  intro z hz
  exact isOpen_ball.is_const_of_fderiv_eq_zero (𝕜 := ℝ)
    (convex_ball x r).isPreconnected
    (fun y hy => (hD y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hD y hy).fderiv) hz (mem_ball_self hr)

/-- Localization by an indicator preserves every derivative test supported
inside the localization set. This is a pointwise identity of integrands. -/
theorem integral_fderiv_smul_indicator_eq_setIntegral
    {U K : Set ℂ} (hU : MeasurableSet U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (ψ : ℂ → ℝ) (hs : tsupport ψ ⊆ K) (v : ℂ) :
    (∫ t, fderiv ℝ ψ t v • K.indicator f t) =
      ∫ t in U, fderiv ℝ ψ t v • f t := by
  rw [← integral_indicator hU]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ K
  · simp [ht, hKU ht]
  · have hD : fderiv ℝ ψ t = 0 :=
      fderiv_of_notMem_tsupport ℝ (fun hm => ht (hs hm))
    by_cases hu : t ∈ U <;> simp [ht, hu, hD]

/-- A derivative of an admissible compact test can be integrated against any
locally integrable function on the open test domain. -/
theorem integrableOn_fderiv_smul_of_locallyIntegrableOn
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U volume)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) (v : ℂ) :
    IntegrableOn (fun t => fderiv ℝ ψ t v • f t) U := by
  have hg : Integrable ((tsupport ψ).indicator f) volume :=
    (integrable_indicator_iff (isClosed_tsupport ψ).measurableSet).mpr
      (hf.integrableOn_compact_subset hs hc)
  have hD : Continuous (fun t => fderiv ℝ ψ t v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hprod := hg.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
    hD (hc.fderiv_apply ℝ v)
  apply (integrable_indicator_iff hU.measurableSet).mp
  apply hprod.congr
  filter_upwards with t
  by_cases ht : t ∈ tsupport ψ
  · simp [ht, hs ht]
  · have hzero : fderiv ℝ ψ t = 0 := fderiv_of_notMem_tsupport ℝ ht
    by_cases hu : t ∈ U <;> simp [ht, hu, hzero]

/-- Compact localization turns local integrability and the original weak
identity into a global locally integrable function and its valid small tests. -/
theorem localized_weakGradientZero
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U volume)
    (hzero : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∀ v : ℂ, ∫ t in U, (fderiv ℝ ψ t v) • f t = 0)
    (x : ℂ) {r : ℝ} (hr : 0 < r) (hKU : closedBall x (3 * r) ⊆ U) :
    LocallyIntegrable ((closedBall x (3 * r)).indicator f) volume ∧
      ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball x (2 * r) → ∀ v : ℂ,
          ∫ t, fderiv ℝ ψ t v • (closedBall x (3 * r)).indicator f t = 0 := by
  constructor
  · have hg : Integrable ((closedBall x (3 * r)).indicator f) volume :=
      (integrable_indicator_iff measurableSet_closedBall).mpr
        (hf.integrableOn_compact_subset hKU (isCompact_closedBall _ _))
    exact hg.locallyIntegrable
  · intro ψ hψ hc hs v
    have hsmall : ball x (2 * r) ⊆ closedBall x (3 * r) := by
      intro t ht
      change dist t x ≤ 3 * r
      have ht' : dist t x < 2 * r := ht
      linarith
    rw [integral_fderiv_smul_indicator_eq_setIntegral hU.measurableSet hKU
      f ψ (hs.trans hsmall)]
    exact hzero ψ hψ hc (hs.trans (hsmall.trans hKU)) v

end GapFamily.Analytic
