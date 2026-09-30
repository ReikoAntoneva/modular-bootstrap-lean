import GapFamily.Analytic.Spatial.SpatialCayleyInverse
import GapFamily.Analytic.Spatial.SpatialDiskIntegral
import GapFamily.Analytic.Modular.Geometry.ModularSeamCoordinateMeasure
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set MeasureTheory Metric UpperHalfPlane

/-- The actual real differential of the inverse Cayley map. -/
def cayleyPointDerivative (ζ : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ (2 * Complex.I / (1 - ζ) ^ 2)).restrictScalars ℝ

theorem cayleyPointDerivative_hasFDerivAt {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    HasFDerivAt cayleyToUpper (cayleyPointDerivative ζ) ζ :=
  (cayleyToUpper_hasDerivAt hζ).hasFDerivAt.restrictScalars ℝ

theorem cayleyPointDerivative_det (ζ : ℂ) :
    (cayleyPointDerivative ζ).det = 4 / Complex.normSq (1 - ζ) ^ 2 := by
  simp [cayleyPointDerivative, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, map_mul, map_pow]
  norm_num

/-- The literal point kernel with a test function, in Euclidean upper coordinates. -/
def pointTestEuclideanDensity (s : ℝ) (F : UpperHalfPlane → ℂ) (z : ℂ) : ℂ :=
  (z.im ^ 2)⁻¹ • (pointKernel (s : ℂ) z Complex.I * F (ofComplex z))

/-- The actual Cayley Jacobian cancels the hyperbolic density and leaves precisely
(1−r²)^(s−2), including the original quarter normalization of the point kernel. -/
theorem cayley_pointTest_density (s : ℝ) (F : UpperHalfPlane → ℂ)
    {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    |(cayleyPointDerivative ζ).det| • pointTestEuclideanDensity s F (cayleyToUpper ζ) =
      (spatialDiskDensity s ζ : ℂ) * F (cayleyUpper ζ) := by
  have hreal (z : ℂ) (hz : 0 < z.im) : pointKernel (s : ℂ) z Complex.I =
      ((1 / 4 * pointParameter z Complex.I ^ (-s) : ℝ) : ℂ) := by
    rw [pointKernel, Complex.ofReal_mul,
      Complex.ofReal_cpow (pointParameter_pos hz (by norm_num)).le]
    simp
  have hcore : |(cayleyPointDerivative ζ).det| •
      ((cayleyToUpper ζ).im ^ 2)⁻¹ • pointKernel (s : ℂ) (cayleyToUpper ζ) Complex.I =
      (spatialDiskDensity s ζ : ℂ) := by
    have ha : 0 < 1 - Complex.normSq ζ := sub_pos.mpr (cayleyToUpper_normSq_lt_one hζ)
    have hb : Complex.normSq (1 - ζ) ≠ 0 :=
      (Complex.normSq_pos.mpr (cayleyToUpper_den_ne_zero hζ)).ne'
    rw [cayleyPointDerivative_det, abs_of_nonneg (by positivity),
      hreal _ (cayleyToUpper_im_pos hζ), cayleyToUpper_im,
      pointParameter_cayleyToUpper_I hζ]
    simp only [Complex.real_smul, ← Complex.ofReal_mul]
    congr 1
    rw [spatialDiskDensity, ← Complex.normSq_eq_norm_sq, Real.rpow_sub ha, Real.rpow_two]
    simp only [one_div]
    rw [← Real.rpow_neg_eq_inv_rpow, neg_neg]
    field_simp [ha.ne', hb]
  simpa only [pointTestEuclideanDensity, cayleyUpper, smul_mul_assoc] using
    congrArg (fun v : ℂ => v * F (ofComplex (cayleyToUpper ζ))) hcore

theorem pointTest_density_cancel (s : ℝ) (F : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    τ.im ^ 2 • pointTestEuclideanDensity s F τ = pointKernel (s : ℂ) τ Complex.I * F τ := by
  simp only [pointTestEuclideanDensity, UpperHalfPlane.coe_im, ofComplex_apply, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 2 τ.im_pos.ne'), one_smul]

/-- Ordinary integrability is preserved by the actual Cayley substitution for any test function. -/
theorem integrable_pointKernel_test_iff_cayley (s : ℝ) (F : UpperHalfPlane → ℂ) :
    Integrable (fun τ : UpperHalfPlane => pointKernel (s : ℂ) τ Complex.I * F τ) volume ↔
      IntegrableOn (fun ζ : ℂ => (spatialDiskDensity s ζ : ℂ) * F (cayleyUpper ζ)) (ball 0 1) := by
  have hh := integrableOn_upperHalfPlane_im_sq_smul_iff
    isOpen_upperHalfPlaneSet.measurableSet (fun z hz => hz) (pointTestEuclideanDensity s F)
  have hh' : Integrable (fun τ : UpperHalfPlane => pointKernel (s : ℂ) τ Complex.I * F τ) volume ↔
      IntegrableOn (pointTestEuclideanDensity s F) upperHalfPlaneSet := by
    simpa only [show UpperHalfPlane.coe ⁻¹' upperHalfPlaneSet = Set.univ from by
      ext τ; simp [τ.im_pos], IntegrableOn, Measure.restrict_univ, pointTest_density_cancel] using hh
  rw [hh', ← cayleyToUpper_image_ball,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure ℂ)
      measurableSet_ball (fun ζ hζ =>
        (cayleyPointDerivative_hasFDerivAt (by simpa using hζ)).hasFDerivWithinAt)
      cayleyToUpper_injOn_ball]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with ζ hζ
  exact cayley_pointTest_density s F (by simpa using hζ)

/-- Exact ordinary-integral Cayley transport. The companion equivalence supplies
ordinary convergence whenever either side is integrable. -/
theorem integral_pointKernel_test_eq_cayley (s : ℝ) (F : UpperHalfPlane → ℂ) :
    (∫ τ : UpperHalfPlane, pointKernel (s : ℂ) τ Complex.I * F τ) =
      ∫ ζ : ℂ in ball 0 1, (spatialDiskDensity s ζ : ℂ) * F (cayleyUpper ζ) := by
  have hh := setIntegral_eq_upperHalfPlane_im_sq_smul
    isOpen_upperHalfPlaneSet.measurableSet (fun z hz => hz) (pointTestEuclideanDensity s F)
  have hh' : (∫ τ : UpperHalfPlane, pointKernel (s : ℂ) τ Complex.I * F τ) =
      ∫ z : ℂ in upperHalfPlaneSet, pointTestEuclideanDensity s F z := by
    simpa only [show UpperHalfPlane.coe ⁻¹' upperHalfPlaneSet = Set.univ from by
      ext τ; simp [τ.im_pos], setIntegral_univ, pointTest_density_cancel] using hh.symm
  rw [hh', ← cayleyToUpper_image_ball,
    integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure ℂ)
      measurableSet_ball (fun ζ hζ =>
        (cayleyPointDerivative_hasFDerivAt (by simpa using hζ)).hasFDerivWithinAt)
      cayleyToUpper_injOn_ball]
  apply setIntegral_congr_fun measurableSet_ball
  intro ζ hζ
  exact cayley_pointTest_density s F (by simpa using hζ)

end GapFamily.Analytic.SpatialPoint
