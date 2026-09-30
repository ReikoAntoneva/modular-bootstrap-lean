import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdH1
import GapFamily.Analytic.Poincare.PoincareHighCuspHessian

/-! Genuine local weak H2 data for the canonical full threshold seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdJet
open Set MeasureTheory UpperHalfPlane ModularGradient Homogenization ModularElliptic
  PoincareCanonical LocalPoisson
open scoped ContDiff

/-- The actual residual jet and the smooth high-cusp lift give real and imaginary
H1 witnesses with genuine weak Hessians on a common centered half cube. -/
theorem exists_thresholdSeed_centered_hessian_data
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (J : ℤ) (z : ℂ) (hz : z ∈ U) :
    ∃ Q : TriadicCube 2, cubeCenter Q = 0 ∧
      ellipticChart z '' scaledClosedCubeSet Q 1 ⊆ U ∧
      ∃ (uR uI : H1Function (scaledOpenCubeSet Q (1 / 2)))
        (_HR : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uR)
        (_HI : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uI),
        uR.toFun =ᵐ[volume.restrict (scaledOpenCubeSet Q (1 / 2))]
          (fun v => (thresholdSeed J (ofComplex (ellipticChart z v))).re) ∧
        uI.toFun =ᵐ[volume.restrict (scaledOpenCubeSet Q (1 / 2))]
          (fun v => (thresholdSeed J (ofComplex (ellipticChart z v))).im) := by
  obtain ⟨j, hj⟩ := exists_thresholdResidualJet χ hχ hc hs U hU hχU J
  obtain ⟨Q, hcenter, hQU, uR, uI, HR, HI, hRv, hIv, _hRg, _hIg⟩ :=
    LocalPoisson.exists_centered_hessian_data U hU j z hz
  let S := scaledOpenCubeSet Q (1 / 2)
  have hS : IsOpen S := by
    change IsOpen (scaledOpenCubeSet Q (1 / 2))
    rw [scaledOpenCubeSet_eq_metricBall Q (by norm_num : (0 : ℝ) < 1 / 2)]
    exact Metric.isOpen_ball
  have hSU : ellipticChart z '' S ⊆ U := by
    rintro w ⟨v, hv, rfl⟩
    apply hQU
    refine ⟨v, ?_, rfl⟩
    intro i
    exact (hv i).le.trans (mul_le_mul_of_nonneg_right
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (cubeRadius_pos Q).le)
  let bR := highCuspChartH1 J χ hχ hc hs Complex.reCLM z S hS
  let bI := highCuspChartH1 J χ hχ hc hs Complex.imCLM z S hS
  refine ⟨Q, hcenter, hQU, uR + bR, uI + bI,
    addWeakHessian HR (highCuspChartHessian J χ hχ hc hs Complex.reCLM z S hS),
    addWeakHessian HI (highCuspChartHessian J χ hχ hc hs Complex.imCLM z S hS), ?_, ?_⟩
  · exact chartH1_high_value_ae χ hχ hc hs U hU hχU J j hj Complex.reCLM z S hS hSU uR hRv
  · exact chartH1_high_value_ae χ hχ hc hs U hU hχU J j hj Complex.imCLM z S hS hSU uI hIv

/-- At every upper point, the canonical full threshold seed itself has local
real and imaginary H1 representatives carrying actual weak L² Hessians.
No cutoff, first-gradient, Sobolev, or Hessian witness is a hypothesis. -/
theorem exists_thresholdSeed_local_hessian_data (J : ℤ) (τ : UpperHalfPlane) :
    ∃ Q : TriadicCube 2, cubeCenter Q = 0 ∧
      ellipticChart (τ : ℂ) '' scaledClosedCubeSet Q 1 ⊆ upperHalfPlaneSet ∧
      ∃ (uR uI : H1Function (scaledOpenCubeSet Q (1 / 2)))
        (_HR : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uR)
        (_HI : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uI),
        uR.toFun =ᵐ[volume.restrict (scaledOpenCubeSet Q (1 / 2))]
          (fun v => (thresholdSeed J (ofComplex (ellipticChart (τ : ℂ) v))).re) ∧
        uI.toFun =ᵐ[volume.restrict (scaledOpenCubeSet Q (1 / 2))]
          (fun v => (thresholdSeed J (ofComplex (ellipticChart (τ : ℂ) v))).im) := by
  obtain ⟨L, U, χ, _hL, _hreg, hτL, hU, hLU, _hUc, hUH, hχ, hc, hs, hχU⟩ :=
    exists_upperEvaluationCutoff (K := ({(τ : ℂ)} : Set ℂ)) isCompact_singleton
      (singleton_subset_upper τ)
  have hτU : (τ : ℂ) ∈ U := hLU (interior_subset (hτL (Set.mem_singleton _)))
  obtain ⟨Q, hcenter, hQU, uR, uI, HR, HI, hRv, hIv⟩ :=
    exists_thresholdSeed_centered_hessian_data χ hχ hc hs U hU hχU J τ hτU
  exact ⟨Q, hcenter, hQU.trans (subset_closure.trans hUH), uR, uI, HR, HI, hRv, hIv⟩

/-- A smaller full open cube provides the standard geometry for subsequent
interior differentiation and elliptic bootstrap, retaining the literal seed values. -/
theorem exists_thresholdSeed_openCube_hessian_data (J : ℤ) (τ : UpperHalfPlane) :
    ∃ Q : TriadicCube 2, cubeCenter Q = 0 ∧
      ellipticChart (τ : ℂ) '' scaledClosedCubeSet Q 1 ⊆ upperHalfPlaneSet ∧
      ∃ (uR uI : H1Function (openCubeSet Q))
        (_HR : HasWeakHessianOn (openCubeSet Q) uR)
        (_HI : HasWeakHessianOn (openCubeSet Q) uI),
        uR.toFun =ᵐ[volume.restrict (openCubeSet Q)]
          (fun v => (thresholdSeed J (ofComplex (ellipticChart (τ : ℂ) v))).re) ∧
        uI.toFun =ᵐ[volume.restrict (openCubeSet Q)]
          (fun v => (thresholdSeed J (ofComplex (ellipticChart (τ : ℂ) v))).im) := by
  obtain ⟨Q₀, hcenter₀, hQ₀H, uR, uI, HR, HI, hRv, hIv⟩ :=
    exists_thresholdSeed_local_hessian_data J τ
  let S := scaledOpenCubeSet Q₀ (1 / 2)
  have hS : IsOpen S := by
    rw [show S = Metric.ball (cubeCenter Q₀) ((1 / 2) * cubeRadius Q₀) from
      scaledOpenCubeSet_eq_metricBall Q₀ (by norm_num : (0 : ℝ) < 1 / 2)]
    exact Metric.isOpen_ball
  have hzero : (0 : Fin 2 → ℝ) ∈ S := by
    rw [show S = Metric.ball (cubeCenter Q₀) ((1 / 2) * cubeRadius Q₀) from
      scaledOpenCubeSet_eq_metricBall Q₀ (by norm_num : (0 : ℝ) < 1 / 2), hcenter₀]
    exact Metric.mem_ball_self (mul_pos (by norm_num) (cubeRadius_pos Q₀))
  obtain ⟨Q, hcenter, hQS, _⟩ := exists_centered_cube_closed_subset hS hzero
  have hopen : IsOpen (openCubeSet Q) := isOpen_openCubeSet Q
  have hsub : openCubeSet Q ⊆ S := by
    intro v hv
    apply hQS
    have hv' : v ∈ scaledOpenCubeSet Q 1 := by
      simpa only [scaledOpenCubeSet_eq_metricBall Q (by norm_num : (0 : ℝ) < 1),
        one_mul, ball_cubeCenter_eq_openCubeSet] using hv
    exact fun i => (hv' i).le
  have hQH : ellipticChart (τ : ℂ) '' scaledClosedCubeSet Q 1 ⊆ upperHalfPlaneSet := by
    rintro w ⟨v, hv, rfl⟩
    apply hQ₀H
    refine ⟨v, ?_, rfl⟩
    have hvS := hQS hv
    intro i
    exact (hvS i).le.trans (mul_le_mul_of_nonneg_right
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (cubeRadius_pos Q₀).le)
  refine ⟨Q, hcenter, hQH, uR.restrict hopen hsub, uI.restrict hopen hsub,
    HR.restrict hopen hsub, HI.restrict hopen hsub, ?_, ?_⟩
  · exact ae_restrict_of_ae_restrict_of_subset hsub hRv
  · exact ae_restrict_of_ae_restrict_of_subset hsub hIv

end GapFamily.Analytic.PoincareThresholdJet
