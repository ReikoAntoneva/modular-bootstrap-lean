import BTZEntropy.Analytic.ComplexKernel
import BTZEntropy.Analytic.SaddlePhase
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Uniform bound for the kernel transform on vertical contours

The nonnegative smoothing kernel bounds its complex Laplace transform by
the real transform at the real part. Compact real intervals therefore give
bounds independent of the contour height.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

theorem norm_complexKernelTransform_le (φ : SmoothKernel) (z : ℂ) :
    ‖complexKernelTransform φ z‖ ≤ kernelTransform φ z.re := by
  calc
    ‖complexKernelTransform φ z‖ ≤
        ∫ u : ℝ, ‖(φ u : ℂ) * (u : ℂ) ^ 0 * Complex.exp (z * u)‖ :=
      norm_integral_le_integral_norm _
    _ = kernelTransform φ z.re := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp [Complex.norm_exp, Complex.mul_re, abs_of_nonneg (φ.nonneg u)]

theorem continuous_complexKernelTransform_contour (φ : SmoothKernel) (β : ℝ) :
    Continuous (fun t : ℝ => complexKernelTransform φ (saddleContour β t)) := by
  exact (differentiable_complexKernelMoment φ 0).continuous.comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

theorem complexKernelTransform_contour_bounded (φ : SmoothKernel) (βmin βmax : ℝ) :
    ∃ C > 0, ∀ β ∈ Set.Icc βmin βmax, ∀ t : ℝ,
      ‖complexKernelTransform φ (saddleContour β t)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    (isCompact_Icc.image (contDiff_kernelTransform φ).continuous).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun β hβ t => ?_⟩
  have hreal : ‖kernelTransform φ β‖ ≤ C := hbound _ ⟨β, hβ, rfl⟩
  have hcomplex := norm_complexKernelTransform_le φ (saddleContour β t)
  rw [saddleContour_re] at hcomplex
  rw [Real.norm_eq_abs] at hreal
  exact hcomplex.trans ((le_abs_self _).trans hreal)

/-- The quadratic denominator supplies an integrable envelope for the full contour. -/
theorem integrable_contour_majorant {βmin : ℝ} (hβmin : 0 < βmin) :
    Integrable (fun t : ℝ => (βmin ^ 2 + t ^ 2)⁻¹) := by
  have hb : βmin ≠ 0 := ne_of_gt hβmin
  have hi := (integrable_inv_one_add_mul_sq (inv_ne_zero hb)).const_mul (βmin ^ 2)⁻¹
  apply hi.congr
  filter_upwards [] with t
  have hsum : βmin ^ 2 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hone : 1 + (βmin⁻¹ * t) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp

end BTZEntropy
