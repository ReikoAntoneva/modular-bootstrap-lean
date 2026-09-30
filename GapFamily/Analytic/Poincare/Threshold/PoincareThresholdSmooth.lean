import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdAllOrders
import GapFamily.Analytic.Elliptic.WeakSobolevSmooth

/-! Actual classical smoothness of the canonical full zero-energy threshold seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdSmooth
open Set MeasureTheory Homogenization UpperHalfPlane ModularElliptic
  PoincareCanonical PoincareThresholdJet EllipticSobolev
  PoincareThresholdAllOrders
open scoped ContDiff

/-- The actual canonical threshold seed has every classical spatial derivative
at each upper point. All weak derivative orders come from its proved local equation. -/
theorem contDiffAt_thresholdSeed (J : ℤ) (τ : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (fun w : ℂ => thresholdSeed J (ofComplex w)) (τ : ℂ) := by
  obtain ⟨Q, hcenter, hQH, horder⟩ := exists_thresholdSeed_chart_allOrders J τ
  have hsub : openCubeSet Q ⊆ scaledClosedCubeSet Q 1 := by
    intro v hv
    have hv' : v ∈ scaledOpenCubeSet Q 1 := by
      simpa only [scaledOpenCubeSet_eq_metricBall Q (by norm_num : (0 : ℝ) < 1),
        one_mul, ball_cubeCenter_eq_openCubeSet] using hv
    exact fun i => (hv' i).le
  have hcont : ContinuousOn ofComplex upperHalfPlaneSet := by
    apply ofComplex.continuousOn.mono
    intro z hz
    simpa [ofComplex] using hz
  have hFc : ContinuousOn (fun v => thresholdSeed J (ofComplex (ellipticChart (τ : ℂ) v)))
      (openCubeSet Q) :=
    ((continuous_thresholdSeed J).comp_continuousOn hcont).comp
      (ellipticChart_contDiff (τ : ℂ)).continuous.continuousOn
      (fun v hv => hQH ⟨v, hsub hv, rfl⟩)
  have hR : ContDiffAt ℝ ∞
      (fun v => (thresholdSeed J (ofComplex (ellipticChart (τ : ℂ) v))).re) 0 := by
    apply contDiffAt_infty_zero_of_local_weakSobolev (Complex.continuous_re.comp_continuousOn hFc)
    intro n
    obtain ⟨V, hV, h0V, hVQ, hRV, hIV⟩ := horder n
    exact ⟨V, hV, h0V, hVQ, hRV⟩
  have hI : ContDiffAt ℝ ∞
      (fun v => (thresholdSeed J (ofComplex (ellipticChart (τ : ℂ) v))).im) 0 := by
    apply contDiffAt_infty_zero_of_local_weakSobolev (Complex.continuous_im.comp_continuousOn hFc)
    intro n
    obtain ⟨V, hV, h0V, hVQ, hRV, hIV⟩ := horder n
    exact ⟨V, hV, h0V, hVQ, hIV⟩
  have hcomplex : ContDiffAt ℝ ∞
      (fun v => thresholdSeed J (ofComplex (ellipticChart (τ : ℂ) v))) 0 := by
    have h := (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hR).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hI).mul (contDiffAt_const (c := Complex.I)))
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.re_add_im] using h
  rw [← ellipticChart_symm_center (τ : ℂ)] at hcomplex
  have hcomp := hcomplex.comp (τ : ℂ) (ellipticChart_symm_contDiff (τ : ℂ)).contDiffAt
  simpa only [Function.comp_def, ellipticChart_symm_center, Homeomorph.apply_symm_apply] using hcomp

/-- Classical C-infinity regularity throughout the upper half-plane, including
the modular side and circular seams, of the canonical full threshold seed. -/
theorem contDiffOn_thresholdSeed (J : ℤ) :
    ContDiffOn ℝ ∞ (fun w : ℂ => thresholdSeed J (ofComplex w)) upperHalfPlaneSet := by
  intro w hw
  exact (contDiffAt_thresholdSeed J ⟨w, hw⟩).contDiffWithinAt

end GapFamily.Analytic.PoincareThresholdSmooth
