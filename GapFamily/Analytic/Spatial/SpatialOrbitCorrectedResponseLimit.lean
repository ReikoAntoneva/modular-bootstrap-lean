import GapFamily.Analytic.Spatial.SpatialOrbitThresholdSourceAverage

/-! Parameter convergence of the actual compact corrected response to its
canonical threshold kernel. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter UpperHalfPlane
open UpperWeightedCoherence
open scoped Topology

/-- The explicit compact response is analytic wherever its actual evaluator
and its genuinely convergent shifted source are both analytic. -/
theorem analyticAt_spatialOrbitCompactResponse_parameter
    {K : Set ℂ} [CompactSpace K] (D : Evaluation (1 / 4) (by norm_num) K)
    (w : UpperHalfPlane) {s : ℂ} (hs : 0 < s.re)
    (hn : ‖s - 1 / 2‖ < D.radius) :
    AnalyticAt ℂ (fun t => spatialOrbitCompactResponse D t w) s := by
  have hκ : s - (1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) D.radius := by
    simpa only [Metric.mem_ball, dist_zero_right] using hn
  have hoperator : AnalyticAt ℂ (fun t : ℂ => D.family (t - 1 / 2)) s :=
    (D.analytic_family _ hκ).comp (f := fun t : ℂ => t - 1 / 2) (x := s)
      (analyticAt_id.sub analyticAt_const)
  exact ((ContinuousLinearMap.apply ℂ C(K, ℂ)).analyticAt_bilinear _).comp₂
    (analyticAt_spatialOrbitThresholdInput w hs) hoperator

theorem analyticAt_spatialOrbitCorrectedResponse_parameter
    {K : Set ℂ} [CompactSpace K] (D : Evaluation (1 / 4) (by norm_num) K)
    (w : UpperHalfPlane) {s : ℂ} (hs : 0 < s.re)
    (hn : ‖s - 1 / 2‖ < D.radius) (hne : s ≠ 1) :
    AnalyticAt ℂ
      (fun t => spatialOrbitCorrectedEvaluation (spatialOrbitCompactResponse D) t w) s :=
  (analyticAt_spatialOrbitCompactResponse_parameter D w hs hn).sub
    ((analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr hne)).smul analyticAt_const)

/-- The real physical parameter approaches a continuous compact response at
one half; no bounded unweighted threshold resolvent is asserted. -/
theorem continuousAt_spatialOrbitCorrectedResponse_parameter_half
    {K : Set ℂ} [CompactSpace K] (D : Evaluation (1 / 4) (by norm_num) K)
    (w : UpperHalfPlane) :
    ContinuousAt
      (fun s : ℝ => spatialOrbitCorrectedEvaluation (spatialOrbitCompactResponse D) (s : ℂ) w)
      (1 / 2) := by
  have hcomplex : ContinuousAt
      (fun s : ℂ => spatialOrbitCorrectedEvaluation (spatialOrbitCompactResponse D) s w)
      (((1 / 2 : ℝ) : ℂ)) := by
    apply (analyticAt_spatialOrbitCorrectedResponse_parameter D w _ _ _).continuousAt
    · norm_num
    · simpa using D.radius_pos
    · norm_num
  exact hcomplex.comp Complex.continuous_ofReal.continuousAt

/-- Each compact corrected threshold observation is exactly the canonical
corrected kernel, independently of every evaluation choice. -/
theorem spatialOrbitCorrectedResponse_half_apply
    {K : Set ℂ} [CompactSpace K] (D : Evaluation (1 / 4) (by norm_num) K)
    (z w : UpperHalfPlane) (hz : (z : ℂ) ∈ K) :
    spatialOrbitCorrectedEvaluation (spatialOrbitCompactResponse D) (1 / 2) w
        ⟨(z : ℂ), hz⟩ = spatialThresholdCorrectedKernel z w := by
  rw [spatialOrbitCorrectedEvaluation_half]
  change spatialOrbitCompactResponse D (1 / 2) w ⟨(z : ℂ), hz⟩ + 6 =
    spatialThresholdKernel z w + 6
  rw [spatialOrbitCompactResponse_half_apply D z w hz]

/-- Scalar entries converge to the same canonical corrected threshold kernel;
in particular this applies along the physical side `s > 1/2`. -/
theorem tendsto_spatialOrbitCorrectedResponse_half_apply
    {K : Set ℂ} [CompactSpace K] (D : Evaluation (1 / 4) (by norm_num) K)
    (z w : UpperHalfPlane) (hz : (z : ℂ) ∈ K) :
    Tendsto
      (fun s : ℝ => spatialOrbitCorrectedEvaluation (spatialOrbitCompactResponse D)
        (s : ℂ) w ⟨(z : ℂ), hz⟩)
      (𝓝 (1 / 2)) (𝓝 (spatialThresholdCorrectedKernel z w)) := by
  have hc := (ContinuousMap.evalCLM ℂ (⟨(z : ℂ), hz⟩ : K) :
    C(K, ℂ) →L[ℂ] ℂ).continuous.continuousAt.comp
    (continuousAt_spatialOrbitCorrectedResponse_parameter_half D w)
  have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  simpa only [ContinuousAt, Function.comp_def, ContinuousMap.evalCLM_apply, hhalf,
    spatialOrbitCorrectedResponse_half_apply D z w hz] using hc

end GapFamily.Analytic.SpatialPoint
