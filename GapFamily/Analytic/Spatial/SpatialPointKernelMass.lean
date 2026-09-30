import GapFamily.Analytic.Spatial.SpatialCayleyGeometry
import GapFamily.Analytic.Spatial.SpatialDiskIntegral
import GapFamily.Analytic.Modular.Geometry.ModularSeamCoordinateMeasure
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
The exact mass of the normalized point kernel at the center I, in the actual
whole upper-half-plane hyperbolic volume. Cayley transport establishes ordinary
integrability as well as the integral identity.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set MeasureTheory Metric UpperHalfPlane

private def cayleyRealDerivative (ζ : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ (2 * Complex.I / (1 - ζ) ^ 2)).restrictScalars ℝ

private theorem cayleyRealDerivative_hasFDerivAt {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    HasFDerivAt cayleyToUpper (cayleyRealDerivative ζ) ζ :=
  (cayleyToUpper_hasDerivAt hζ).hasFDerivAt.restrictScalars ℝ

private theorem cayleyRealDerivative_det (ζ : ℂ) :
    (cayleyRealDerivative ζ).det = 4 / Complex.normSq (1 - ζ) ^ 2 := by
  simp [cayleyRealDerivative, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, map_mul, map_pow]
  norm_num

private def pointKernelEuclideanDensity (s : ℝ) (z : ℂ) : ℂ :=
  (z.im ^ 2)⁻¹ • pointKernel (s : ℂ) z Complex.I

private theorem pointKernel_real (s : ℝ) {z : ℂ} (hz : 0 < z.im) :
    pointKernel (s : ℂ) z Complex.I =
      ((1 / 4 * pointParameter z Complex.I ^ (-s) : ℝ) : ℂ) := by
  rw [pointKernel, Complex.ofReal_mul, Complex.ofReal_cpow
    (pointParameter_pos hz (by norm_num)).le]
  simp

private theorem cayley_pointKernel_density (s : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    |(cayleyRealDerivative ζ).det| •
        pointKernelEuclideanDensity s (cayleyToUpper ζ) =
      (spatialDiskDensity s ζ : ℂ) := by
  have ha : 0 < 1 - Complex.normSq ζ :=
    sub_pos.mpr (cayleyToUpper_normSq_lt_one hζ)
  have hb : Complex.normSq (1 - ζ) ≠ 0 :=
    (Complex.normSq_pos.mpr (cayleyToUpper_den_ne_zero hζ)).ne'
  rw [cayleyRealDerivative_det, abs_of_nonneg (by positivity),
    pointKernelEuclideanDensity, pointKernel_real s (cayleyToUpper_im_pos hζ),
    cayleyToUpper_im, pointParameter_cayleyToUpper_I hζ]
  simp only [Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  rw [spatialDiskDensity, ← Complex.normSq_eq_norm_sq,
    Real.rpow_sub ha, Real.rpow_two]
  simp only [one_div]
  rw [← Real.rpow_neg_eq_inv_rpow, neg_neg]
  field_simp [ha.ne', hb]

private theorem integrableOn_pointKernelEuclideanDensity (s : ℝ) (hs : 1 < s) :
    IntegrableOn (pointKernelEuclideanDensity s) upperHalfPlaneSet := by
  rw [← cayleyToUpper_image_ball,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure ℂ)
      measurableSet_ball (fun ζ hζ =>
        (cayleyRealDerivative_hasFDerivAt (by simpa using hζ)).hasFDerivWithinAt)
      cayleyToUpper_injOn_ball]
  apply (integrableOn_spatialDiskDensity_complex hs).congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with ζ hζ
  exact (cayley_pointKernel_density s (by simpa using hζ)).symm

private theorem integral_pointKernelEuclideanDensity (s : ℝ) (hs : 1 < s) :
    (∫ z in upperHalfPlaneSet, pointKernelEuclideanDensity s z) =
      (Real.pi / (s - 1) : ℝ) := by
  rw [← cayleyToUpper_image_ball,
    integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure ℂ)
      measurableSet_ball (fun ζ hζ =>
        (cayleyRealDerivative_hasFDerivAt (by simpa using hζ)).hasFDerivWithinAt)
      cayleyToUpper_injOn_ball]
  calc
    _ = ∫ ζ : ℂ in ball 0 1, (spatialDiskDensity s ζ : ℂ) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro ζ hζ
      exact cayley_pointKernel_density s (by simpa using hζ)
    _ = _ := integral_spatialDiskDensity_complex hs

private theorem pointKernel_density_cancel (s : ℝ) (τ : UpperHalfPlane) :
    τ.im ^ 2 • pointKernelEuclideanDensity s τ = pointKernel (s : ℂ) τ Complex.I := by
  simp only [pointKernelEuclideanDensity, UpperHalfPlane.coe_im, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 2 τ.im_pos.ne'), one_smul]

/-- The actual whole-half-plane kernel is ordinarily integrable for real s > 1. -/
theorem integrable_pointKernel_I (s : ℝ) (hs : 1 < s) :
    Integrable (fun τ : UpperHalfPlane => pointKernel (s : ℂ) τ Complex.I) := by
  have h := (integrableOn_upperHalfPlane_im_sq_smul_iff
    isOpen_upperHalfPlaneSet.measurableSet (fun z hz => hz)
    (pointKernelEuclideanDensity s)).mpr (integrableOn_pointKernelEuclideanDensity s hs)
  simpa only [show UpperHalfPlane.coe ⁻¹' upperHalfPlaneSet = Set.univ from by
    ext τ; simp [τ.im_pos], IntegrableOn, Measure.restrict_univ,
    pointKernel_density_cancel] using h

/-- Its exact mass is π/(s−1), with normalization 1/4 independent of s. -/
theorem integral_pointKernel_I (s : ℝ) (hs : 1 < s) :
    (∫ τ : UpperHalfPlane, pointKernel (s : ℂ) τ Complex.I) =
      (Real.pi / (s - 1) : ℝ) := by
  have h := setIntegral_eq_upperHalfPlane_im_sq_smul
    isOpen_upperHalfPlaneSet.measurableSet (fun z hz => hz)
    (pointKernelEuclideanDensity s)
  rw [integral_pointKernelEuclideanDensity s hs] at h
  simpa only [show UpperHalfPlane.coe ⁻¹' upperHalfPlaneSet = Set.univ from by
    ext τ; simp [τ.im_pos], setIntegral_univ, pointKernel_density_cancel] using h.symm

end GapFamily.Analytic.SpatialPoint
