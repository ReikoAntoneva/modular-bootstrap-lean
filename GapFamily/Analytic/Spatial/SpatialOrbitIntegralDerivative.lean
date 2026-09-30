import GapFamily.Analytic.Spatial.SpatialOrbitRowIntegrable
import GapFamily.Analytic.Spatial.SpatialOrbitFrameMeasurable
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff MatrixGroups

/-- The literal ordinary integral representative of the actual orbit operator. -/
def spatialOrbitIntegralFunction (s : ℝ) (f : ModularHilbert) (z : ℂ) : ℂ :=
  ∫ w : UpperHalfPlane, spatialOrbitKernel (s : ℂ) (UpperHalfPlane.ofComplex z) w * f w ∂modularMeasure

private theorem integral_ball_height (z₀ : UpperHalfPlane) {z : ℂ}
    (hz : z ∈ Metric.ball (z₀ : ℂ) (z₀.im / 2)) : z₀.im / 2 < z.im := by
  have hn : ‖z - (z₀ : ℂ)‖ < z₀.im / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hi := (Complex.abs_im_le_norm (z - (z₀ : ℂ))).trans_lt hn
  simp only [Complex.sub_im] at hi
  have hlo := (abs_lt.mp hi).1
  change -(z₀.im / 2) < z.im - z₀.im at hlo
  linarith

/-- A true L¹ row supplies a uniform local majorant for the derivative integrand. -/
theorem spatialOrbitIntegral_derivative_local_bound (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (z₀ : UpperHalfPlane) {z : ℂ}
    (hz : z ∈ Metric.ball (z₀ : ℂ) (z₀.im / 2)) (w : UpperHalfPlane) :
    ‖f w • fderiv ℝ (fun v : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex v) w) z‖ ≤
      ((2 * s / z₀.im) * (8 : ℝ)^s) * ‖spatialOrbitKernel (s : ℂ) z₀ w * f w‖ := by
  have hheight := integral_ball_height z₀ hz
  have hzH : 0 < z.im := (half_pos z₀.im_pos).trans hheight
  let z' : UpperHalfPlane := ⟨z, hzH⟩
  have hn : ‖(z' : ℂ) - (z₀ : ℂ)‖ ≤ z₀.im / 2 := by
    exact (show ‖z - (z₀ : ℂ)‖ < z₀.im / 2 by
      simpa only [Metric.mem_ball, dist_eq_norm] using hz).le
  have hs0 : 0 ≤ s := by linarith
  have hframe := spatialOrbitKernel_frame_fderiv_norm_le (s : ℂ) (by simpa using hs) z' w
  simp only [Complex.ofReal_re, Complex.norm_of_nonneg hs0] at hframe
  have hvalue := (spatialOrbitKernel_norm_local_comparison s hs z₀ z' w hn).1
  have hb : (z₀.im / 2) *
      ‖fderiv ℝ (fun v : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex v) w) z‖ ≤
      s * ((8 : ℝ)^s * ‖spatialOrbitKernel (s : ℂ) z₀ w‖) :=
    ((mul_le_mul_of_nonneg_right hheight.le (norm_nonneg _)).trans hframe).trans
      (mul_le_mul_of_nonneg_left hvalue hs0)
  have hD : ‖fderiv ℝ (fun v : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex v) w) z‖ ≤
      (s * ((8 : ℝ)^s * ‖spatialOrbitKernel (s : ℂ) z₀ w‖)) / (z₀.im / 2) :=
    (le_div_iff₀ (half_pos z₀.im_pos)).mpr (by simpa only [mul_comm] using hb)
  rw [norm_smul]
  calc
    _ ≤ ‖f w‖ * ((s * ((8 : ℝ)^s * ‖spatialOrbitKernel (s : ℂ) z₀ w‖)) / (z₀.im / 2)) :=
      mul_le_mul_of_nonneg_left hD (norm_nonneg _)
    _ = _ := by rw [norm_mul]; field_simp

private theorem spatialOrbitIntegral_derivative_measurable (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (z : UpperHalfPlane) :
    AEStronglyMeasurable (fun w : UpperHalfPlane => f w •
      fderiv ℝ (fun v : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex v) w) (z : ℂ)) modularMeasure :=
  (Lp.memLp f).aestronglyMeasurable.smul
    (((continuous_spatialOrbit_fderiv_left (s : ℂ) (by simpa using hs)).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)

/-- The actual continuous-linear derivative operator is ordinarily integrable in every row. -/
theorem integrable_spatialOrbitIntegral_derivative (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (z : UpperHalfPlane) :
    Integrable (fun w : UpperHalfPlane => f w •
      fderiv ℝ (fun v : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex v) w) (z : ℂ)) modularMeasure := by
  apply ((integrable_spatialOrbitKernel_mul s hs f z).norm.const_mul
    ((2 * s / z.im) * (8 : ℝ)^s)).mono'
    (spatialOrbitIntegral_derivative_measurable s hs f z)
  exact Filter.Eventually.of_forall
    (spatialOrbitIntegral_derivative_local_bound s hs f z
      (Metric.mem_ball_self (half_pos z.im_pos)))

/-- Differentiation under the literal orbit integral is valid for every modular L² input. -/
theorem hasFDerivAt_spatialOrbitIntegralFunction (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (z : UpperHalfPlane) :
    HasFDerivAt (spatialOrbitIntegralFunction s f)
      (∫ w : UpperHalfPlane, f w •
        fderiv ℝ (fun v : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex v) w) (z : ℂ)
        ∂modularMeasure) (z : ℂ) := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball (z : ℂ) (z.im / 2))
    (F := fun v : ℂ => fun w : UpperHalfPlane => spatialOrbitKernel (s : ℂ) (ofComplex v) w * f w)
    (F' := fun v : ℂ => fun w : UpperHalfPlane => f w •
      fderiv ℝ (fun v : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex v) w) v)
    (bound := fun w => ((2 * s / z.im) * (8 : ℝ)^s) * ‖spatialOrbitKernel (s : ℂ) z w * f w‖)
    (Metric.ball_mem_nhds _ (half_pos z.im_pos))
  · exact Filter.Eventually.of_forall fun v =>
      (((continuous_spatialOrbitKernel (s : ℂ) (by simpa using hs)).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul (Lp.memLp f).aestronglyMeasurable
  · simpa only [UpperHalfPlane.ofComplex_apply] using integrable_spatialOrbitKernel_mul s hs f z
  · exact spatialOrbitIntegral_derivative_measurable s hs f z
  · exact Filter.Eventually.of_forall fun w v hv =>
      spatialOrbitIntegral_derivative_local_bound s hs f z hv w
  · exact (integrable_spatialOrbitKernel_mul s hs f z).norm.const_mul _
  · apply Filter.Eventually.of_forall
    intro w v hv
    have hvH : 0 < v.im := (half_pos z.im_pos).trans (integral_ball_height z hv)
    have hd := (hasFDerivAt_spatialOrbitKernel (s : ℂ) (by simpa using hs) ⟨v, hvH⟩ w).differentiableAt.hasFDerivAt
    have hd' : HasFDerivAt
        (fun x : ℂ => f w * spatialOrbitKernel (s : ℂ) (ofComplex x) w)
        (f w • fderiv ℝ (fun x : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex x) w) v) v :=
      hd.const_smul (f w)
    convert hd' using 1
    funext x
    exact mul_comm _ _

/-- The displayed operator-valued integral is the actual Fréchet derivative. -/
theorem fderiv_spatialOrbitIntegralFunction (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (z : UpperHalfPlane) :
    fderiv ℝ (spatialOrbitIntegralFunction s f) (z : ℂ) =
      ∫ w : UpperHalfPlane, f w •
        fderiv ℝ (fun v : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex v) w) (z : ℂ)
        ∂modularMeasure :=
  (hasFDerivAt_spatialOrbitIntegralFunction s hs f z).fderiv

/-- The operator-valued derivative integral is continuous at every upper point. -/
theorem continuousAt_spatialOrbitIntegral_derivative (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (z : UpperHalfPlane) :
    ContinuousAt (fun v : ℂ => ∫ w : UpperHalfPlane, f w •
      fderiv ℝ (fun u : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex u) w) v
      ∂modularMeasure) (z : ℂ) := by
  apply MeasureTheory.continuousAt_of_dominated
    (bound := fun w => ((2 * s / z.im) * (8 : ℝ)^s) * ‖spatialOrbitKernel (s : ℂ) z w * f w‖)
  · filter_upwards [Metric.ball_mem_nhds (z : ℂ) (half_pos z.im_pos)] with v hv
    have hvH : 0 < v.im := (half_pos z.im_pos).trans (integral_ball_height z hv)
    exact spatialOrbitIntegral_derivative_measurable s hs f ⟨v, hvH⟩
  · filter_upwards [Metric.ball_mem_nhds (z : ℂ) (half_pos z.im_pos)] with v hv
    exact Filter.Eventually.of_forall (spatialOrbitIntegral_derivative_local_bound s hs f z hv)
  · exact (integrable_spatialOrbitKernel_mul s hs f z).norm.const_mul _
  · exact Filter.Eventually.of_forall fun w =>
      ((contDiffAt_spatialOrbitKernel_left (s : ℂ) (by simpa using hs) z w).continuousAt_fderiv
        (by norm_num)).const_smul (f w)

/-- Every modular L² input gives an actual C¹ ordinary integral representative. -/
theorem contDiffAt_spatialOrbitIntegralFunction (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (z : UpperHalfPlane) :
    ContDiffAt ℝ 1 (spatialOrbitIntegralFunction s f) (z : ℂ) := by
  apply contDiffAt_one_iff.mpr
  refine ⟨(fun v : ℂ => ∫ w : UpperHalfPlane, f w •
    fderiv ℝ (fun u : ℂ => spatialOrbitKernel (s : ℂ) (ofComplex u) w) v ∂modularMeasure),
    upperHalfPlaneSet, isOpen_upperHalfPlaneSet.mem_nhds z.im_pos, ?_, ?_⟩
  · intro v hv
    exact (continuousAt_spatialOrbitIntegral_derivative s hs f ⟨v, hv⟩).continuousWithinAt
  · intro v hv
    exact hasFDerivAt_spatialOrbitIntegralFunction s hs f ⟨v, hv⟩

/-- C¹ regularity holds on the entire upper half-plane, including all modular seams. -/
theorem contDiffOn_spatialOrbitIntegralFunction (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) :
    ContDiffOn ℝ 1 (spatialOrbitIntegralFunction s f) upperHalfPlaneSet := by
  intro z hz
  exact (contDiffAt_spatialOrbitIntegralFunction s hs f ⟨z, hz⟩).contDiffWithinAt

end GapFamily.Analytic.SpatialPoint
