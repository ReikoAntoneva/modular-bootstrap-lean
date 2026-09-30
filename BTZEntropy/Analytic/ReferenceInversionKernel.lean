import BTZEntropy.Analytic.ReferenceKernelSchwartz
import BTZEntropy.Analytic.SaddlePhase
import Mathlib.Analysis.Fourier.Inversion

/-! Fourier inversion for the actual compact smoothing kernel on a vertical Laplace contour. -/

noncomputable section

namespace BTZEntropy

open MeasureTheory
open scoped FourierTransform

theorem complexKernelTransform_eq_fourierInv (φ : SmoothKernel) (β t : ℝ) :
    complexKernelTransform φ (saddleContour β t) =
      𝓕⁻ (tiltedKernelSchwartz φ β : ℝ → ℂ) (t / (2 * Real.pi)) := by
  rw [Real.fourierInv_eq']
  unfold complexKernelTransform complexKernelMoment
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [pow_zero, mul_one, RCLike.inner_apply, conj_trivial, smul_eq_mul]
  rw [tiltedKernelSchwartz_apply]
  have he : (((2 * Real.pi * ((t / (2 * Real.pi)) * u) : ℝ) : ℂ) * Complex.I) =
      (t : ℂ) * Complex.I * (u : ℂ) := by
    push_cast
    field_simp
  rw [he]
  rw [show saddleContour β t * (u : ℂ) =
    (β : ℂ) * (u : ℂ) + (t : ℂ) * Complex.I * (u : ℂ) by
      unfold saddleContour; ring, Complex.exp_add]
  ring

theorem complexKernelTransform_scaled_eq_fourierInv (φ : SmoothKernel) (β t : ℝ) :
    complexKernelTransform φ (saddleContour β (2 * Real.pi * t)) =
      𝓕⁻ (tiltedKernelSchwartz φ β : ℝ → ℂ) t := by
  rw [complexKernelTransform_eq_fourierInv]
  field_simp

theorem integrable_complexKernelTransform_contour (φ : SmoothKernel) (β : ℝ) :
    Integrable (fun t : ℝ => complexKernelTransform φ (saddleContour β t)) := by
  simp_rw [complexKernelTransform_eq_fourierInv]
  apply (integrable_comp_div_iff _ (by positivity : 2 * Real.pi ≠ 0)).2
  simpa only [← SchwartzMap.fourierInv_coe] using (𝓕⁻ (tiltedKernelSchwartz φ β)).integrable

/-- The ordinary inverse-Laplace kernel for a state at energy `x`. -/
def kernelInverseIntegrand (φ : SmoothKernel) (β E x t : ℝ) : ℂ :=
  Complex.exp (saddleContour β t * ((E - x : ℝ) : ℂ)) *
    complexKernelTransform φ (saddleContour β t)

theorem norm_kernelInverseExponent (β E x t : ℝ) :
    ‖Complex.exp (saddleContour β t * ((E - x : ℝ) : ℂ))‖ =
      Real.exp (β * (E - x)) := by
  rw [Complex.norm_exp]
  simp

theorem integrable_kernelInverseIntegrand (φ : SmoothKernel) (β E x : ℝ) :
    Integrable (kernelInverseIntegrand φ β E x) := by
  apply (integrable_complexKernelTransform_contour φ β).bdd_mul
  · exact (Complex.continuous_exp.comp
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).mul
        continuous_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => (norm_kernelInverseExponent β E x t).le

theorem tiltedKernel_fourier_inversion (φ : SmoothKernel) (β y : ℝ) :
    (φ y : ℂ) * Complex.exp ((β : ℂ) * (y : ℂ)) =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, Complex.exp (-(t : ℂ) * Complex.I * (y : ℂ)) *
          complexKernelTransform φ (saddleContour β t) := by
  let f := tiltedKernelSchwartz φ β
  let g : ℝ → ℂ := fun t => Complex.exp (-(t : ℂ) * Complex.I * (y : ℂ)) *
    complexKernelTransform φ (saddleContour β t)
  have hinv : 𝓕 (𝓕⁻ (f : ℝ → ℂ)) y = f y := by
    exact f.integrable.fourier_fourierInv_eq
      (by simpa only [← SchwartzMap.fourier_coe] using (𝓕 f).integrable)
      f.continuous.continuousAt
  calc
    _ = 𝓕 (𝓕⁻ (f : ℝ → ℂ)) y := hinv.symm
    _ = ∫ t : ℝ, g (2 * Real.pi * t) := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [g, f]
      rw [complexKernelTransform_scaled_eq_fourierInv]
      simp only [conj_trivial]
      congr 2
      push_cast
      ring
    _ = _ := by
      rw [Measure.integral_comp_mul_left]
      rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi))]
      simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
        Complex.ofReal_ofNat, one_div]
      rfl

/-- Pointwise Fourier inversion for the actual smoothing kernel, on any real vertical line. -/
theorem kernel_fourier_inversion (φ : SmoothKernel) (β E x : ℝ) :
    (φ (x - E) : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, kernelInverseIntegrand φ β E x t := by
  have hinv := tiltedKernel_fourier_inversion φ β (x - E)
  have hexp : Complex.exp ((β : ℂ) * ((x - E : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  apply (mul_right_cancel₀ hexp)
  rw [hinv]
  rw [mul_assoc, ← integral_mul_const]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  unfold kernelInverseIntegrand
  have he : saddleContour β t * ((E - x : ℝ) : ℂ) +
      (β : ℂ) * ((x - E : ℝ) : ℂ) =
      -(t : ℂ) * Complex.I * ((x - E : ℝ) : ℂ) := by
    unfold saddleContour
    push_cast
    ring
  calc
    _ = Complex.exp (saddleContour β t * ((E - x : ℝ) : ℂ) +
        (β : ℂ) * ((x - E : ℝ) : ℂ)) *
          complexKernelTransform φ (saddleContour β t) := by rw [he]
    _ = _ := by rw [Complex.exp_add]; ring

end BTZEntropy
