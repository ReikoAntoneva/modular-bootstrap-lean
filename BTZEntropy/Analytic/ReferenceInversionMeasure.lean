import BTZEntropy.Analytic.ReferenceInversionKernel
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier smoothing of a thermally integrable weighted measure

This is a genuine Fubini theorem: an ordinary weighted physical count equals its
inverse thermal contour. The hypotheses are measurable energy and weight and one
absolute thermal moment; no spectral or inversion equality is assumed.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- The actual Laplace transform of a weighted energy distribution. -/
def weightedComplexLaplace (μ : Measure α) (energy weight : α → ℝ) (z : ℂ) : ℂ :=
  ∫ q, (weight q : ℂ) * Complex.exp (-z * energy q) ∂μ

/-- The actual physical smoothing of the same weighted energy distribution. -/
def weightedSmoothCount (φ : SmoothKernel) (μ : Measure α)
    (energy weight : α → ℝ) (E : ℝ) : ℝ :=
  ∫ q, weight q * φ (energy q - E) ∂μ

omit [MeasurableSpace α] in
private theorem norm_weightedInverseIntegrand (φ : SmoothKernel) (β E : ℝ)
    (energy weight : α → ℝ) (q : α) (t : ℝ) :
    ‖(weight q : ℂ) * Complex.exp (saddleContour β t * ((E - energy q : ℝ) : ℂ)) *
      complexKernelTransform φ (saddleContour β t)‖ =
      Real.exp (β * E) *
        (‖weight q * Real.exp (-β * energy q)‖ *
          ‖complexKernelTransform φ (saddleContour β t)‖) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_kernelInverseExponent]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← mul_assoc, ← mul_assoc]
  have he : Real.exp (β * (E - energy q)) =
      Real.exp (β * E) * Real.exp (-β * energy q) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

omit [SFinite μ] in
/-- The two-dimensional inversion integrand is absolutely integrable. -/
theorem integrable_weightedInverseIntegrand (φ : SmoothKernel) (β E : ℝ)
    (energy weight : α → ℝ) (he : Measurable energy) (hw : Measurable weight)
    (hthermal : Integrable (fun q => weight q * Real.exp (-β * energy q)) μ) :
    Integrable (fun p : α × ℝ => (weight p.1 : ℂ) *
      Complex.exp (saddleContour β p.2 * ((E - energy p.1 : ℝ) : ℂ)) *
        complexKernelTransform φ (saddleContour β p.2)) (μ.prod volume) := by
  have hK := integrable_complexKernelTransform_contour φ β
  have hi := (hthermal.norm.mul_prod hK.norm).const_mul (Real.exp (β * E))
  apply hi.mono'
  · have hc : Measurable (saddleContour β) := by unfold saddleContour; fun_prop
    have hk : Measurable (fun t : ℝ => complexKernelTransform φ (saddleContour β t)) :=
      (differentiable_complexKernelMoment φ 0).continuous.measurable.comp hc
    exact (((Complex.measurable_ofReal.comp (hw.comp measurable_fst)).mul
      (Complex.measurable_exp.comp ((hc.comp measurable_snd).mul
        (Complex.measurable_ofReal.comp (measurable_const.sub (he.comp measurable_fst)))))).mul
      (hk.comp measurable_snd)).aestronglyMeasurable
  · filter_upwards [] with p
    exact (norm_weightedInverseIntegrand φ β E energy weight p.1 p.2).le

/-- Exact inverse-contour representation of a genuine physical smoothing. -/
theorem weightedSmoothCount_eq_contour (φ : SmoothKernel) (β E : ℝ)
    (energy weight : α → ℝ) (he : Measurable energy) (hw : Measurable weight)
    (hthermal : Integrable (fun q => weight q * Real.exp (-β * energy q)) μ) :
    (weightedSmoothCount φ μ energy weight E : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        Complex.exp (saddleContour β t * E) * complexKernelTransform φ (saddleContour β t) *
          weightedComplexLaplace μ energy weight (saddleContour β t) := by
  let f : α × ℝ → ℂ := fun p => (weight p.1 : ℂ) *
    Complex.exp (saddleContour β p.2 * ((E - energy p.1 : ℝ) : ℂ)) *
      complexKernelTransform φ (saddleContour β p.2)
  have hf : Integrable f (μ.prod volume) :=
    integrable_weightedInverseIntegrand φ β E energy weight he hw hthermal
  have hpoint (q : α) :
      ((weight q * φ (energy q - E) : ℝ) : ℂ) =
        (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, f (q, t) := by
    rw [Complex.ofReal_mul, kernel_fourier_inversion φ β E (energy q)]
    dsimp only [f, kernelInverseIntegrand]
    simp_rw [mul_assoc (weight q : ℂ)]
    rw [integral_const_mul]
    ring
  have hinner (t : ℝ) : (∫ q, f (q, t) ∂μ) =
      Complex.exp (saddleContour β t * E) * complexKernelTransform φ (saddleContour β t) *
        weightedComplexLaplace μ energy weight (saddleContour β t) := by
    rw [weightedComplexLaplace, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with q
    dsimp only [f]
    rw [show saddleContour β t * ((E - energy q : ℝ) : ℂ) =
      saddleContour β t * (E : ℂ) + (-saddleContour β t * (energy q : ℂ)) by
        push_cast; ring, Complex.exp_add]
    ring
  calc
    _ = ∫ q, ((weight q * φ (energy q - E) : ℝ) : ℂ) ∂μ := by
      rw [integral_complex_ofReal]
      rfl
    _ = ∫ q, ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, f (q, t)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ q, (∫ t : ℝ, f (q, t)) ∂μ :=
      integral_const_mul _ _
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, ∫ q, f (q, t) ∂μ := by
      rw [integral_integral_swap hf]
    _ = _ := by simp_rw [hinner]

omit [SFinite μ] in
/-- The physical smoothing is itself absolutely integrable. -/
theorem integrable_weightedSmoothCount (φ : SmoothKernel) (β E : ℝ)
    (energy weight : α → ℝ) (he : Measurable energy) (hw : Measurable weight)
    (hthermal : Integrable (fun q => weight q * Real.exp (-β * energy q)) μ) :
    Integrable (fun q => weight q * φ (energy q - E)) μ := by
  let f : α × ℝ → ℂ := fun p => (weight p.1 : ℂ) *
    Complex.exp (saddleContour β p.2 * ((E - energy p.1 : ℝ) : ℂ)) *
      complexKernelTransform φ (saddleContour β p.2)
  have hf : Integrable f (μ.prod volume) :=
    integrable_weightedInverseIntegrand φ β E energy weight he hw hthermal
  have hpoint (q : α) :
      ((weight q * φ (energy q - E) : ℝ) : ℂ) =
        (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, f (q, t) := by
    rw [Complex.ofReal_mul, kernel_fourier_inversion φ β E (energy q)]
    dsimp only [f, kernelInverseIntegrand]
    simp_rw [mul_assoc (weight q : ℂ)]
    rw [integral_const_mul]
    ring
  apply ((hf.integral_prod_left.const_mul (1 / (2 * Real.pi) : ℂ)).re).congr
  filter_upwards [] with q
  rw [← hpoint]
  rfl

/-- The inverse contour obtained from the actual weighted measure is absolutely integrable. -/
theorem integrable_weightedInverseContour (φ : SmoothKernel) (β E : ℝ)
    (energy weight : α → ℝ) (he : Measurable energy) (hw : Measurable weight)
    (hthermal : Integrable (fun q => weight q * Real.exp (-β * energy q)) μ) :
    Integrable (fun t : ℝ =>
      Complex.exp (saddleContour β t * E) * complexKernelTransform φ (saddleContour β t) *
        weightedComplexLaplace μ energy weight (saddleContour β t)) := by
  have hf := integrable_weightedInverseIntegrand φ β E energy weight he hw hthermal
  apply hf.integral_prod_right.congr
  filter_upwards [] with t
  rw [weightedComplexLaplace, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [show saddleContour β t * ((E - energy q : ℝ) : ℂ) =
    saddleContour β t * (E : ℂ) + (-saddleContour β t * (energy q : ℂ)) by
      push_cast; ring, Complex.exp_add]
  ring

end BTZEntropy
