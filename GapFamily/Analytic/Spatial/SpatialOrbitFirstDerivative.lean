import GapFamily.Analytic.Spatial.SpatialOrbitNormal
import GapFamily.Analytic.Spatial.SpatialPointFirstBound
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Actual first spatial derivatives of the orbit kernel

The existing summable center values bound all derivative operators on an
ordinary upper-half-plane ball. Their uniformly convergent sum is the actual
real derivative of the half-normalized orbit kernel and is continuous there.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter UpperHalfPlane
open scoped Topology ContDiff MatrixGroups

private theorem spatial_ball_height (z₀ : UpperHalfPlane) {z : ℂ}
    (hz : z ∈ Metric.ball (z₀ : ℂ) (z₀.im / 2)) : z₀.im / 2 < z.im := by
  have hn : ‖z - (z₀ : ℂ)‖ < z₀.im / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hi := (Complex.abs_im_le_norm (z - (z₀ : ℂ))).trans_lt hn
  simp only [Complex.sub_im] at hi
  have hlo := (abs_lt.mp hi).1
  change -(z₀.im / 2) < z.im - z₀.im at hlo
  linarith

/-- A genuine summable bound for all term derivative operators on one ordinary ball. -/
theorem exists_spatialOrbit_fderiv_majorant (s : ℂ) (hs : 1 < s.re)
    (z₀ w : UpperHalfPlane) :
    ∃ u : SL(2, ℤ) → ℝ, Summable u ∧ (∀ γ, 0 ≤ u γ) ∧
      ∀ (γ : SL(2, ℤ)) (z : ℂ), z ∈ Metric.ball (z₀ : ℂ) (z₀.im / 2) →
        ‖fderiv ℝ (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane)) z‖ ≤ u γ := by
  let a : SL(2, ℤ) → ℝ := fun γ =>
    (8 : ℝ) ^ s.re * ‖pointKernel (s.re : ℂ) z₀ (γ • w : UpperHalfPlane)‖
  let C : ℝ := (2 * ‖s‖) / (z₀.im / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : Summable a := (summable_norm_spatialOrbit_real s.re hs z₀ w).mul_left _
  refine ⟨fun γ => C * a γ, ha.mul_left C, fun γ => mul_nonneg hC (by dsimp [a]; positivity), ?_⟩
  intro γ z hz
  have hheight := spatial_ball_height z₀ hz
  have hzH : 0 < z.im := (half_pos z₀.im_pos).trans hheight
  let z' : UpperHalfPlane := ⟨z, hzH⟩
  have hn : ‖z - (z₀ : ℂ)‖ ≤ z₀.im / 2 := by
    exact (show ‖z - (z₀ : ℂ)‖ < z₀.im / 2 by
      simpa only [Metric.mem_ball, dist_eq_norm] using hz).le
  have hval : ‖pointKernel s z (γ • w : UpperHalfPlane)‖ ≤ a γ := by
    change ‖pointKernel s z' (γ • w : UpperHalfPlane)‖ ≤ _
    rw [norm_pointKernel_eq_realPart]
    exact (pointKernel_norm_local_comparison (by linarith : 0 ≤ s.re)
      z₀ z' (γ • w) hn).1
  have hframe := pointKernel_frame_fderiv_norm_le s hzH (γ • w : UpperHalfPlane).im_pos
  have hb : (z₀.im / 2) *
      ‖fderiv ℝ (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane)) z‖ ≤
      (2 * ‖s‖) * a γ :=
    ((mul_le_mul_of_nonneg_right hheight.le (norm_nonneg _)).trans hframe).trans
      (mul_le_mul_of_nonneg_left hval (by positivity))
  calc
    _ ≤ ((2 * ‖s‖) * a γ) / (z₀.im / 2) :=
      (le_div_iff₀ (half_pos z₀.im_pos)).mpr (by simpa only [mul_comm] using hb)
    _ = C * a γ := by dsimp [C]; ring

/-- The actual derivative series is norm summable at every upper point. -/
theorem summable_norm_spatialOrbit_fderiv (s : ℂ) (hs : 1 < s.re)
    (z₀ w : UpperHalfPlane) :
    Summable (fun γ : SL(2, ℤ) =>
      ‖fderiv ℝ (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane)) (z₀ : ℂ)‖) := by
  obtain ⟨u, hu, _hu0, hub⟩ := exists_spatialOrbit_fderiv_majorant s hs z₀ w
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun γ => hub γ z₀ (Metric.mem_ball_self (half_pos z₀.im_pos))) hu

/-- The derivative partial sums converge uniformly on an actual ordinary upper ball. -/
theorem tendstoUniformlyOn_spatialOrbit_fderiv (s : ℂ) (hs : 1 < s.re)
    (z₀ w : UpperHalfPlane) :
    TendstoUniformlyOn
      (fun t : Finset (SL(2, ℤ)) => fun z : ℂ =>
        ∑ γ ∈ t, fderiv ℝ (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane)) z)
      (fun z => ∑' γ : SL(2, ℤ),
        fderiv ℝ (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane)) z)
      atTop (Metric.ball (z₀ : ℂ) (z₀.im / 2)) := by
  obtain ⟨u, hu, _hu0, hub⟩ := exists_spatialOrbit_fderiv_majorant s hs z₀ w
  exact tendstoUniformlyOn_tsum hu hub

/-- Termwise differentiation of the actual orbit kernel, with its exact half normalization. -/
theorem hasFDerivAt_spatialOrbitKernel (s : ℂ) (hs : 1 < s.re)
    (z₀ w : UpperHalfPlane) :
    HasFDerivAt (fun z : ℂ => spatialOrbitKernel s (UpperHalfPlane.ofComplex z) w)
      ((1 / 2 : ℂ) • ∑' γ : SL(2, ℤ),
        fderiv ℝ (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane)) (z₀ : ℂ))
      (z₀ : ℂ) := by
  obtain ⟨u, hu, _hu0, hub⟩ := exists_spatialOrbit_fderiv_majorant s hs z₀ w
  have hf : ∀ (γ : SL(2, ℤ)) (z : ℂ), z ∈ Metric.ball (z₀ : ℂ) (z₀.im / 2) →
      HasFDerivAt (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane))
        (fderiv ℝ (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane)) z) z := by
    intro γ z hz
    exact ((pointKernel_contDiffAt_left s
      ((half_pos z₀.im_pos).trans (spatial_ball_height z₀ hz))
      (γ • w : UpperHalfPlane).im_pos).differentiableAt (by simp)).hasFDerivAt
  have hsum := hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (z₀ : ℂ) (z₀.im / 2)).isPreconnected hf hub
    (Metric.mem_ball_self (half_pos z₀.im_pos))
    (summable_spatialOrbit s hs z₀ w) (Metric.mem_ball_self (half_pos z₀.im_pos))
  apply (hsum.const_mul (1 / 2 : ℂ)).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (z₀ : ℂ) (half_pos z₀.im_pos)] with z hz
  have hzH := (half_pos z₀.im_pos).trans (spatial_ball_height z₀ hz)
  simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hzH] using
    spatialOrbitKernel_eq_half_tsum_right s (UpperHalfPlane.ofComplex z) w

theorem fderiv_spatialOrbitKernel (s : ℂ) (hs : 1 < s.re)
    (z₀ w : UpperHalfPlane) :
    fderiv ℝ (fun z : ℂ => spatialOrbitKernel s (UpperHalfPlane.ofComplex z) w) (z₀ : ℂ) =
      (1 / 2 : ℂ) • ∑' γ : SL(2, ℤ),
        fderiv ℝ (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane)) (z₀ : ℂ) :=
  (hasFDerivAt_spatialOrbitKernel s hs z₀ w).fderiv

/-- The actual derivative is continuous, so the orbit kernel is C1 in its first point. -/
theorem contDiffAt_spatialOrbitKernel_left (s : ℂ) (hs : 1 < s.re)
    (z₀ w : UpperHalfPlane) :
    ContDiffAt ℝ 1 (fun z : ℂ => spatialOrbitKernel s (UpperHalfPlane.ofComplex z) w) (z₀ : ℂ) := by
  obtain ⟨u, hu, _hu0, hub⟩ := exists_spatialOrbit_fderiv_majorant s hs z₀ w
  have hD : ContinuousOn
      (fun z => ∑' γ : SL(2, ℤ),
        fderiv ℝ (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane)) z)
      (Metric.ball (z₀ : ℂ) (z₀.im / 2)) := by
    apply continuousOn_tsum _ hu hub
    intro γ
    have hterm : ContDiffOn ℝ ∞
        (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane))
        (Metric.ball (z₀ : ℂ) (z₀.im / 2)) := by
      intro z hz
      exact (pointKernel_contDiffAt_left s
        ((half_pos z₀.im_pos).trans (spatial_ball_height z₀ hz))
        (γ • w : UpperHalfPlane).im_pos).contDiffWithinAt
    exact hterm.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)
  apply contDiffAt_one_iff.mpr
  refine ⟨fun z => (1 / 2 : ℂ) • ∑' γ : SL(2, ℤ),
    fderiv ℝ (fun v : ℂ => pointKernel s v (γ • w : UpperHalfPlane)) z,
    Metric.ball (z₀ : ℂ) (z₀.im / 2),
    Metric.ball_mem_nhds (z₀ : ℂ) (half_pos z₀.im_pos), ?_, ?_⟩
  · have hc : ContinuousOn (fun _ : ℂ => (1 / 2 : ℂ))
        (Metric.ball (z₀ : ℂ) (z₀.im / 2)) := continuousOn_const
    exact hc.smul hD
  · intro z hz
    exact hasFDerivAt_spatialOrbitKernel s hs
      ⟨z, (half_pos z₀.im_pos).trans (spatial_ball_height z₀ hz)⟩ w

theorem contDiffOn_spatialOrbitKernel_left (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    ContDiffOn ℝ 1 (fun z : ℂ => spatialOrbitKernel s (UpperHalfPlane.ofComplex z) w)
      upperHalfPlaneSet := by
  intro z hz
  exact (contDiffAt_spatialOrbitKernel_left s hs ⟨z, hz⟩ w).contDiffWithinAt

end GapFamily.Analytic.SpatialPoint
