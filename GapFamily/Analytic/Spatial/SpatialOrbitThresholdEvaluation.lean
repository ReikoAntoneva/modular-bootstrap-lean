import GapFamily.Analytic.Foundation.UpperWeightedThresholdValue
import GapFamily.Analytic.Spatial.SpatialOrbitWeightedAnalytic
import GapFamily.Analytic.Spatial.SpatialOrbitWeightedSourceContinuity
import GapFamily.Analytic.Spatial.SpatialOrbitPointResolvent

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory Metric UpperHalfPlane ModularGradient CuspSchurLocal Dirichlet
open scoped ContDiff Topology
open UpperWeightedCoherence

/-- The actual shifted point source with the fixed admissible cusp weight `α = 1/4`.
Its definition uses only the convergent orbit sum when `0 < re s`. -/
def spatialOrbitThresholdInput (s : ℂ) (w : UpperHalfPlane) : ModularHilbert :=
  s ^ 2 • spatialOrbitWeightedSource (1 / 4) (by norm_num) (by norm_num) (s + 1) w

/-- The threshold evaluates a genuinely convergent row at parameter `3/2`. -/
theorem spatialOrbitThresholdInput_half (w : UpperHalfPlane) :
    spatialOrbitThresholdInput (1 / 2) w =
      (1 / 4 : ℂ) • spatialOrbitWeightedSource (1 / 4) (by norm_num) (by norm_num)
        (3 / 2) w := by
  norm_num [spatialOrbitThresholdInput]

theorem analyticAt_spatialOrbitThresholdInput (w : UpperHalfPlane) {s : ℂ}
    (hs : 0 < s.re) : AnalyticAt ℂ (fun t => spatialOrbitThresholdInput t w) s := by
  have hs1 : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hsource := (analyticAt_spatialOrbitWeightedSource_parameter
    (1 / 4) (by norm_num) (by norm_num) w hs1).comp
      (f := fun t : ℂ => t + 1) (x := s)
      (analyticAt_id.add analyticAt_const : AnalyticAt ℂ (fun t : ℂ => t + 1) s)
  exact (analyticAt_id.pow 2).smul hsource

theorem continuous_spatialOrbitThresholdInput_source (s : ℂ) (hs : 0 < s.re) :
    Continuous (spatialOrbitThresholdInput s) := by
  change Continuous (fun w => s ^ 2 •
    spatialOrbitWeightedSource (1 / 4) (by norm_num) (by norm_num) (s + 1) w)
  have hs1 : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  exact (continuous_spatialOrbitWeightedSource_source (1 / 4) (by norm_num) (by norm_num)
    (s + 1) hs1).const_smul (s ^ 2)

/-- Unweighting recovers the literal shifted source in modular `L²`. -/
theorem cuspWeightedInput_spatialOrbitThresholdInput (s : ℂ) (hs : 0 < s.re)
    (w : UpperHalfPlane) :
    cuspWeightedInput (1 / 4) (by norm_num) (spatialOrbitThresholdInput s w) =
      s ^ 2 • spatialOrbitPointSource (s + 1) w := by
  have hs1 : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  rw [spatialOrbitThresholdInput, map_smul,
    cuspWeightedInput_spatialOrbitWeightedSource_eq_pointSource
      (1 / 4) (by norm_num) (by norm_num) (s + 1) hs1 w]

/-- Canonical threshold spatial kernel, obtained from the constructed weighted
evaluation of the convergent `3/2` source. -/
def spatialThresholdKernel (z w : UpperHalfPlane) : ℂ :=
  weightedThresholdValue (1 / 4) (by norm_num) (spatialOrbitThresholdInput (1 / 2) w) z

/-- Canonical threshold kernel with the actual constant channel removed. -/
def spatialThresholdCorrectedKernel (z w : UpperHalfPlane) : ℂ :=
  spatialThresholdKernel z w + 6

theorem continuous_spatialThresholdKernel_left (w : UpperHalfPlane) :
    Continuous (fun z => spatialThresholdKernel z w) :=
  continuous_weightedThresholdValue (1 / 4) (by norm_num) _

theorem continuous_spatialThresholdCorrectedKernel_left (w : UpperHalfPlane) :
    Continuous (fun z => spatialThresholdCorrectedKernel z w) :=
  (continuous_spatialThresholdKernel_left w).add continuous_const

theorem continuous_spatialThresholdKernel_right (z : UpperHalfPlane) :
    Continuous (spatialThresholdKernel z) :=
  (weightedThresholdEvaluation (1 / 4) (by norm_num) z).continuous.comp
    (continuous_spatialOrbitThresholdInput_source (1 / 2) (by norm_num))

theorem continuous_spatialThresholdCorrectedKernel_right (z : UpperHalfPlane) :
    Continuous (spatialThresholdCorrectedKernel z) :=
  (continuous_spatialThresholdKernel_right z).add continuous_const

/-- Removing the actual constant spectral channel from a compact observed row.
The coefficient is fixed by the modular volume `π/3`. -/
def spatialOrbitCorrectedEvaluation {K : Set ℂ} [CompactSpace K]
    (F : ℂ → UpperHalfPlane → C(K, ℂ)) (s : ℂ) (w : UpperHalfPlane) : C(K, ℂ) :=
  F s w - (3 / (s - 1) : ℂ) • (1 : C(K, ℂ))

/-- The constant-channel subtraction has no pole on this threshold disk. -/
theorem analyticOnNhd_spatialOrbitCorrectedEvaluation {K : Set ℂ} [CompactSpace K]
    (F : ℂ → UpperHalfPlane → C(K, ℂ)) {r : ℝ} (hr : r ≤ 1 / 4)
    (w : UpperHalfPlane)
    (hF : AnalyticOnNhd ℂ (fun s => F s w) (Metric.ball (1 / 2 : ℂ) r)) :
    AnalyticOnNhd ℂ (fun s => spatialOrbitCorrectedEvaluation F s w)
      (Metric.ball (1 / 2 : ℂ) r) := by
  intro s hs
  have hn : ‖s - (1 / 2 : ℂ)‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hs
  have hne : s - 1 ≠ 0 := by
    intro he
    have hs1 : s = 1 := sub_eq_zero.mp he
    rw [hs1] at hn
    norm_num at hn
    linarith
  exact (hF s hs).sub
    ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) hne).smul analyticAt_const)

/-- The mean-zero correction is exactly `+6` at the threshold. -/
theorem spatialOrbitCorrectedEvaluation_half {K : Set ℂ} [CompactSpace K]
    (F : ℂ → UpperHalfPlane → C(K, ℂ)) (w : UpperHalfPlane) :
    spatialOrbitCorrectedEvaluation F (1 / 2) w = F (1 / 2) w + (6 : C(K, ℂ)) := by
  apply ContinuousMap.ext
  intro z
  change F (1 / 2) w z - (3 / ((1 / 2 : ℂ) - 1)) * 1 = F (1 / 2) w z + 6
  norm_num

set_option maxHeartbeats 1000000 in
/-- The actual compactly observed spatial resolvent continues analytically across
`s = 1/2`. The radius and observation chart work for every source point `w`.

The continued object is a continuous function on the requested compact set, not
an unweighted bounded Hilbert-space resolvent at threshold. Its physical-side
identification uses the literal convergent source at `s + 1`, with no assumed
analytic continuation or positivity hypothesis. -/
theorem exists_analytic_spatialOrbitThresholdEvaluation
    (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
      (hsχ : tsupport χ ⊆ upperHalfPlaneSet) (U : Set ℂ) (hU : IsOpen U)
      (hχU : EqOn χ (fun _ => 1) U) (hKU : K ⊆ U)
      (F : ℂ → UpperHalfPlane → C(K, ℂ)) (r : ℝ),
      0 < r ∧ r ≤ 1 / 4 ∧
      (∀ w : UpperHalfPlane,
        AnalyticOnNhd ℂ (fun s => F s w) (Metric.ball (1 / 2 : ℂ) r) ∧
        AnalyticOnNhd ℂ (fun s => spatialOrbitCorrectedEvaluation F s w)
          (Metric.ball (1 / 2 : ℂ) r)) ∧
      (∀ (w z : UpperHalfPlane) (hz : (z : ℂ) ∈ K),
        F (1 / 2) w ⟨(z : ℂ), hz⟩ = spatialThresholdKernel z w ∧
        spatialOrbitCorrectedEvaluation F (1 / 2) w ⟨(z : ℂ), hz⟩ =
          spatialThresholdCorrectedKernel z w) ∧
      ∀ s : ℂ, ‖s - (1 / 2 : ℂ)‖ < r → 1 / 2 < s.re →
        ∀ w : UpperHalfPlane,
          ∃ hu : CuspSchur.actualSchurResolvent (s * (1 - s))
              (s ^ 2 • spatialOrbitPointSource (s + 1) w) ∈ laplacian.domain,
            F s w = laplacianUpperCompactRestriction χ hχ hc hsχ U hU hχU K hKU
              (gradientLift laplacian
                ⟨CuspSchur.actualSchurResolvent (s * (1 - s))
                  (s ^ 2 • spatialOrbitPointSource (s + 1) w), hu⟩) := by
  obtain ⟨D⟩ := nonempty_evaluation K hKH (by norm_num : (0 : ℝ) < 1 / 4)
  let χ := D.cutoff
  have hχ := D.cutoff_smooth
  have hc := D.cutoff_compact
  have hsχ := D.cutoff_support
  let U := D.region
  have hU := D.open_region
  have hχU := D.one_region
  have hKU := D.compact_subset
  let E := D.family
  let ε := D.radius
  have hε := D.radius_pos
  have hE := D.analytic_family
  have hphysical := D.physical
  let r : ℝ := min ε (1 / 4)
  have hr : 0 < r := lt_min hε (by norm_num)
  have hrε : r ≤ ε := min_le_left _ _
  have hrq : r ≤ 1 / 4 := min_le_right _ _
  let F : ℂ → UpperHalfPlane → C(K, ℂ) := fun s w =>
    E (s - 1 / 2) (spatialOrbitThresholdInput s w)
  have hpositive {s : ℂ} (hn : ‖s - (1 / 2 : ℂ)‖ < r) : 0 < s.re := by
    have hnorm := Complex.abs_re_le_norm (s - (1 / 2 : ℂ))
    have hlo := neg_abs_le (s - (1 / 2 : ℂ)).re
    norm_num [Complex.sub_re] at hnorm hlo
    linarith
  have hanalytic (w : UpperHalfPlane) :
      AnalyticOnNhd ℂ (fun s => F s w) (Metric.ball (1 / 2 : ℂ) r) := by
    intro s hs
    have hn : ‖s - (1 / 2 : ℂ)‖ < r := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hs
    have hκ : s - (1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using hn.trans_le hrε
    have hoperator : AnalyticAt ℂ (fun t : ℂ => E (t - 1 / 2)) s :=
      (hE _ hκ).comp (f := fun t : ℂ => t - 1 / 2) (x := s)
        (analyticAt_id.sub analyticAt_const :
        AnalyticAt ℂ (fun t : ℂ => t - 1 / 2) s)
    have hsource := analyticAt_spatialOrbitThresholdInput w (hpositive hn)
    exact ((ContinuousLinearMap.apply ℂ C(K, ℂ)).analyticAt_bilinear _).comp₂
      hsource hoperator
  refine ⟨χ, hχ, hc, hsχ, U, hU, hχU, hKU, F, r, hr, hrq,
    fun w => ⟨hanalytic w, analyticOnNhd_spatialOrbitCorrectedEvaluation F hrq w (hanalytic w)⟩,
    ?_, ?_⟩
  · intro w z hz
    have he : F (1 / 2) w ⟨(z : ℂ), hz⟩ = spatialThresholdKernel z w := by
      simpa only [F, E, sub_self, spatialThresholdKernel] using
        (weightedThresholdValue_eq_evaluation (by norm_num : (0 : ℝ) < 1 / 4)
          D (spatialOrbitThresholdInput (1 / 2) w) z hz).symm
    refine ⟨he, ?_⟩
    rw [spatialOrbitCorrectedEvaluation_half]
    change F (1 / 2) w ⟨(z : ℂ), hz⟩ + 6 = spatialThresholdKernel z w + 6
    exact congrArg (fun c : ℂ => c + 6) he
  · intro s hn hs w
    have hκ : 0 < (s - (1 / 2 : ℂ)).re := by
      norm_num [Complex.sub_re]
      linarith
    obtain ⟨hu, hvalue⟩ := hphysical (s - 1 / 2) (hn.trans_le hrε) hκ
      (spatialOrbitThresholdInput s w)
    have hparameter : parameter (s - (1 / 2 : ℂ)) = s * (1 - s) := by
      dsimp [parameter]
      ring
    have hsource := cuspWeightedInput_spatialOrbitThresholdInput s (hpositive hn) w
    have hres : CuspSchur.actualSchurResolvent (parameter (s - (1 / 2 : ℂ)))
        (cuspWeightedInput (1 / 4) (by norm_num) (spatialOrbitThresholdInput s w)) =
        CuspSchur.actualSchurResolvent (s * (1 - s))
          (s ^ 2 • spatialOrbitPointSource (s + 1) w) := by
      rw [hparameter, hsource]
    refine ⟨hres ▸ hu, ?_⟩
    exact hvalue.trans (congrArg
      (fun u : laplacian.domain =>
        laplacianUpperCompactRestriction χ hχ hc hsχ U hU hχU K hKU
          (gradientLift laplacian u))
      (Subtype.ext hres))

end GapFamily.Analytic.SpatialPoint
