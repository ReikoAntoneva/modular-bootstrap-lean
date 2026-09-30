import GapFamily.Analytic.Modular.ModularLaplacianTest
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Ordinary differentiation of a smooth local Laplacian mollifier

The kernel is a genuine compactly supported smooth function and the convolved
function is locally integrable. All convolutions are ordinary convergent
integrals; no regularity of the original function is assumed.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory Filter Metric ContinuousLinearMap
open scoped ContDiff Convolution Topology

open ModularGradient

/-- The ordinary real-coordinate Laplacian of a complex-valued function. -/
def euclideanLaplacian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  fderiv ℝ (fun w => fderiv ℝ f w 1) z 1 +
    fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z Complex.I

/-- A real smooth kernel convolved with an ordinary complex function. -/
def kernelConvolution (η : ℂ → ℝ) (g : ℂ → ℂ) : ℂ → ℂ :=
  g ⋆[(lsmul ℝ ℝ).flip, volume] η

theorem kernelConvolution_eq_integral (η : ℂ → ℝ) (g : ℂ → ℂ) (y : ℂ) :
    kernelConvolution η g y = ∫ t, η (y - t) • g t := rfl

theorem kernelConvolution_contDiff {η : ℂ → ℝ} {g : ℂ → ℂ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hg : LocallyIntegrable g volume) :
    ContDiff ℝ ∞ (kernelConvolution η g) :=
  hc.contDiff_convolution_right (lsmul ℝ ℝ).flip hg hη

theorem kernelConvolution_integrable {η : ℂ → ℝ} {g : ℂ → ℂ}
    (hη : Continuous η) (hc : HasCompactSupport η)
    (hg : LocallyIntegrable g volume) (y : ℂ) :
    Integrable (fun t => η (y - t) • g t) volume :=
  hc.convolutionExists_right (lsmul ℝ ℝ).flip hg hη y

/-- One actual directional derivative can be moved to the smooth kernel. -/
theorem kernelConvolution_fderiv_apply {η : ℂ → ℝ} {g : ℂ → ℂ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hg : LocallyIntegrable g volume) (y v : ℂ) :
    fderiv ℝ (kernelConvolution η g) y v =
      kernelConvolution (fun z => fderiv ℝ η z v) g y := by
  have hd := hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ).flip hg
    (hη.of_le (by simp)) y
  change (fderiv ℝ (g ⋆[(lsmul ℝ ℝ).flip, volume] η) y) v = _
  rw [hd.fderiv, convolution_precompR_apply (lsmul ℝ ℝ).flip hg
    (hc.fderiv ℝ) (hη.continuous_fderiv (by simp))]
  rfl

/-- The ordinary second directional derivative is convolution with the second kernel derivative. -/
theorem kernelConvolution_second_fderiv_apply {η : ℂ → ℝ} {g : ℂ → ℂ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hg : LocallyIntegrable g volume) (y v w : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ (kernelConvolution η g) z v) y w =
      kernelConvolution (fun z => fderiv ℝ (fun t => fderiv ℝ η t v) z w) g y := by
  have heq : (fun z => fderiv ℝ (kernelConvolution η g) z v) =
      kernelConvolution (fun z => fderiv ℝ η z v) g :=
    funext (fun z => kernelConvolution_fderiv_apply hη hc hg z v)
  rw [heq]
  exact kernelConvolution_fderiv_apply (contDiff_testDerivative η hη v)
    (hc.fderiv_apply ℝ v) hg y w

theorem euclideanTestLaplacian_contDiff {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (euclideanTestLaplacian η) :=
  (contDiff_testDerivative _ (contDiff_testDerivative η hη 1) 1).add
    (contDiff_testDerivative _ (contDiff_testDerivative η hη Complex.I) Complex.I)

theorem euclideanTestLaplacian_hasCompactSupport {η : ℂ → ℝ} (hc : HasCompactSupport η) :
    HasCompactSupport (euclideanTestLaplacian η) :=
  ((hc.fderiv_apply ℝ 1).fderiv_apply ℝ 1).add
    ((hc.fderiv_apply ℝ Complex.I).fderiv_apply ℝ Complex.I)

theorem euclideanTestLaplacian_tsupport_subset (η : ℂ → ℝ) :
    tsupport (euclideanTestLaplacian η) ⊆ tsupport η := by
  apply (tsupport_add _ _).trans
  exact union_subset
    ((tsupport_fderiv_apply_subset ℝ 1).trans (tsupport_fderiv_apply_subset ℝ 1))
    ((tsupport_fderiv_apply_subset ℝ Complex.I).trans (tsupport_fderiv_apply_subset ℝ Complex.I))

/-- The full actual Laplacian passes through the ordinary convolution. -/
theorem kernelConvolution_laplacian {η : ℂ → ℝ} {g : ℂ → ℂ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hg : LocallyIntegrable g volume) (y : ℂ) :
    euclideanLaplacian (kernelConvolution η g) y =
      kernelConvolution (euclideanTestLaplacian η) g y := by
  unfold euclideanLaplacian
  rw [kernelConvolution_second_fderiv_apply hη hc hg,
    kernelConvolution_second_fderiv_apply hη hc hg]
  simp only [kernelConvolution_eq_integral, euclideanTestLaplacian, add_smul]
  rw [integral_add]
  · exact kernelConvolution_integrable
      (contDiff_testDerivative _ (contDiff_testDerivative η hη 1) 1).continuous
      ((hc.fderiv_apply ℝ 1).fderiv_apply ℝ 1) hg y
  · exact kernelConvolution_integrable
      (contDiff_testDerivative _ (contDiff_testDerivative η hη Complex.I) Complex.I).continuous
      ((hc.fderiv_apply ℝ Complex.I).fderiv_apply ℝ Complex.I) hg y

/-- Reflection followed by translation, used to turn a convolution kernel into a test. -/
def laplacianReflectTranslate (y : ℂ) : Homeomorph ℂ ℂ :=
  (Homeomorph.neg ℂ).trans (Homeomorph.addLeft y)

@[simp] theorem laplacianReflectTranslate_apply (y t : ℂ) :
    laplacianReflectTranslate y t = y - t := by
  simp [laplacianReflectTranslate, sub_eq_add_neg]

theorem contDiff_reflected_kernel {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) (y : ℂ) :
    ContDiff ℝ ∞ (fun t => η (y - t)) :=
  hη.comp (contDiff_const.sub contDiff_id)

theorem hasCompactSupport_reflected_kernel {η : ℂ → ℝ}
    (hc : HasCompactSupport η) (y : ℂ) :
    HasCompactSupport (fun t => η (y - t)) := by
  simpa only [Function.comp_def, laplacianReflectTranslate_apply] using
    hc.comp_homeomorph (laplacianReflectTranslate y)

theorem fderiv_reflected_kernel {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) (y t v : ℂ) :
    fderiv ℝ (fun w => η (y - w)) t v = - fderiv ℝ η (y - t) v := by
  have ht : HasFDerivAt (fun w : ℂ => y - w) (- ContinuousLinearMap.id ℝ ℂ) t := by
    simpa using! (hasFDerivAt_const y t).sub (hasFDerivAt_id t)
  have hcomp := ((hη.differentiable (by simp)).differentiableAt.hasFDerivAt).comp t ht
  simpa [Function.comp_def] using congrArg (fun A : ℂ →L[ℝ] ℝ => A v) hcomp.fderiv

theorem second_fderiv_reflected_kernel {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η)
    (y t v w : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ (fun a => η (y - a)) z v) t w =
      fderiv ℝ (fun z => fderiv ℝ η z v) (y - t) w := by
  have heq : (fun z => fderiv ℝ (fun a => η (y - a)) z v) =
      fun z => -(fderiv ℝ η (y - z) v) :=
    funext (fun z => fderiv_reflected_kernel hη y z v)
  rw [heq, fderiv_fun_neg]
  simp only [neg_apply]
  rw [fderiv_reflected_kernel (contDiff_testDerivative η hη v)]
  simp

/-- The two reflection signs cancel in the genuine second-order test operator. -/
theorem laplacian_reflected_kernel {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) (y t : ℂ) :
    euclideanTestLaplacian (fun z => η (y - z)) t = euclideanTestLaplacian η (y - t) := by
  simp only [euclideanTestLaplacian, second_fderiv_reflected_kernel hη]

/-- The weak equation becomes a pointwise equation for the actual smooth convolution,
provided the reflected kernel is an admissible interior test. -/
theorem kernelConvolution_laplacian_of_weak_identity
    {g h : ℂ → ℂ} (hg : LocallyIntegrable g volume)
    (_hh : LocallyIntegrable h volume) {U : Set ℂ}
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      (∫ t, ψ t • h t) = -(∫ t, euclideanTestLaplacian ψ t • g t))
    {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (y : ℂ) (hs : tsupport (fun t => η (y - t)) ⊆ U) :
    euclideanLaplacian (kernelConvolution η g) y = -kernelConvolution η h y := by
  have hw := hweak (fun t => η (y - t)) (contDiff_reflected_kernel hη y)
    (hasCompactSupport_reflected_kernel hc y) hs
  simp_rw [laplacian_reflected_kernel hη] at hw
  rw [kernelConvolution_laplacian hη hc hg]
  simp only [kernelConvolution_eq_integral]
  exact (neg_eq_iff_eq_neg.mp hw.symm)

/-- A small normalized bump reflected about a point of the inner ball stays
strictly inside the doubled ball. -/
theorem normed_reflected_kernel_tsupport_subset_ball
    (x : ℂ) {r : ℝ} (_hr : 0 < r) (φ : ContDiffBump (0 : ℂ))
    (hφ : φ.rOut < r) {y : ℂ} (hy : y ∈ ball x r) :
    tsupport (fun t => φ.normed volume (y - t)) ⊆ ball x (2 * r) := by
  have heq : (fun t => φ.normed volume (y - t)) =
      φ.normed volume ∘ laplacianReflectTranslate y := by
    ext t
    simp
  rw [heq, tsupport_comp_eq_preimage]
  intro t ht
  have hyt : dist t y ≤ φ.rOut := by
    have hm : laplacianReflectTranslate y t ∈ closedBall (0 : ℂ) φ.rOut := by
      simpa only [φ.tsupport_normed_eq, mem_preimage] using ht
    simpa only [mem_closedBall, laplacianReflectTranslate_apply, dist_zero_right,
      ← dist_eq_norm_sub, dist_comm y t] using hm
  have htx := dist_triangle t y x
  have hyx : dist y x < r := hy
  change dist t x < 2 * r
  linarith

/-- Compact localization preserves every ordinary scalar test supported in the localized set. -/
theorem integral_test_smul_indicator_eq_setIntegral
    {U K : Set ℂ} (hU : MeasurableSet U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (ψ : ℂ → ℝ) (hs : tsupport ψ ⊆ K) :
    (∫ t, ψ t • K.indicator f t) = ∫ t in U, ψ t • f t := by
  rw [← integral_indicator hU]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ K
  · simp [ht, hKU ht]
  · have hψ : ψ t = 0 := image_eq_zero_of_notMem_tsupport (fun hm => ht (hs hm))
    by_cases hu : t ∈ U <;> simp [ht, hu, hψ]

/-- An ordinary weak Laplacian equation localizes to genuinely integrable functions. -/
theorem localized_weakLaplacian
    {f h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U volume) (hh : LocallyIntegrableOn h U volume)
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      (∫ t in U, ψ t • h t) = -(∫ t in U, euclideanTestLaplacian ψ t • f t))
    (x : ℂ) {r : ℝ} (hr : 0 < r) (hKU : closedBall x (3 * r) ⊆ U) :
    Integrable ((closedBall x (3 * r)).indicator f) volume ∧
    Integrable ((closedBall x (3 * r)).indicator h) volume ∧
    ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball x (2 * r) →
      (∫ t, ψ t • (closedBall x (3 * r)).indicator h t) =
        -(∫ t, euclideanTestLaplacian ψ t • (closedBall x (3 * r)).indicator f t) := by
  have hsmall : ball x (2 * r) ⊆ closedBall x (3 * r) := by
    intro t ht
    change dist t x ≤ 3 * r
    have ht' : dist t x < 2 * r := ht
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (integrable_indicator_iff measurableSet_closedBall).mpr
      (hf.integrableOn_compact_subset hKU (isCompact_closedBall _ _))
  · exact (integrable_indicator_iff measurableSet_closedBall).mpr
      (hh.integrableOn_compact_subset hKU (isCompact_closedBall _ _))
  · intro ψ hψ hc hs
    rw [integral_test_smul_indicator_eq_setIntegral hU.measurableSet hKU h ψ
      (hs.trans hsmall),
      integral_test_smul_indicator_eq_setIntegral hU.measurableSet hKU f
        (euclideanTestLaplacian ψ) ((euclideanTestLaplacian_tsupport_subset ψ).trans
          (hs.trans hsmall))]
    exact hweak ψ hψ hc (hs.trans (hsmall.trans hKU))

/-- A normalized smooth bump satisfies the actual localized weak Laplacian equation
pointwise on the inner ball. Both convolutions exist as ordinary integrals. -/
theorem normed_kernelConvolution_laplacian_on_ball
    {f h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U volume) (hh : LocallyIntegrableOn h U volume)
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      (∫ t in U, ψ t • h t) = -(∫ t in U, euclideanTestLaplacian ψ t • f t))
    (x : ℂ) {r : ℝ} (hr : 0 < r) (hKU : closedBall x (3 * r) ⊆ U)
    (φ : ContDiffBump (0 : ℂ)) (hφ : φ.rOut < r) :
    ContDiff ℝ ∞ (kernelConvolution (φ.normed volume) ((closedBall x (3 * r)).indicator f)) ∧
    ContDiff ℝ ∞ (kernelConvolution (φ.normed volume) ((closedBall x (3 * r)).indicator h)) ∧
    ∀ y ∈ ball x r,
      Integrable (fun t => φ.normed volume (y - t) •
        (closedBall x (3 * r)).indicator f t) volume ∧
      Integrable (fun t => φ.normed volume (y - t) •
        (closedBall x (3 * r)).indicator h t) volume ∧
      euclideanLaplacian
        (kernelConvolution (φ.normed volume) ((closedBall x (3 * r)).indicator f)) y =
        -kernelConvolution (φ.normed volume) ((closedBall x (3 * r)).indicator h) y := by
  obtain ⟨hfg, hhg, htest⟩ := localized_weakLaplacian hU hf hh hweak x hr hKU
  refine ⟨kernelConvolution_contDiff φ.contDiff_normed φ.hasCompactSupport_normed
      hfg.locallyIntegrable,
    kernelConvolution_contDiff φ.contDiff_normed φ.hasCompactSupport_normed
      hhg.locallyIntegrable, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · exact kernelConvolution_integrable φ.continuous_normed φ.hasCompactSupport_normed
      hfg.locallyIntegrable y
  · exact kernelConvolution_integrable φ.continuous_normed φ.hasCompactSupport_normed
      hhg.locallyIntegrable y
  · exact kernelConvolution_laplacian_of_weak_identity hfg.locallyIntegrable hhg.locallyIntegrable htest
      φ.contDiff_normed φ.hasCompactSupport_normed y
      (normed_reflected_kernel_tsupport_subset_ball x hr φ hφ hy)

end GapFamily.Analytic
