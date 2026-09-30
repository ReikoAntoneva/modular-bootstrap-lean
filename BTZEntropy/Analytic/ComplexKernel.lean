import BTZEntropy.Analytic.Amplitude
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Entire extension of the smoothing transform

The complex transform is the actual compactly supported Laplace integral. Its
derivatives are given by the same moment integrals, and restriction to the real
axis agrees with the transform used to define the BTZ coefficients.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace BTZEntropy

def complexKernelMoment (φ : SmoothKernel) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (φ u : ℂ) * (u : ℂ) ^ n * Complex.exp (z * u)

def complexKernelTransform (φ : SmoothKernel) : ℂ → ℂ := complexKernelMoment φ 0

theorem complexKernelMoment_integrable (φ : SmoothKernel) (n : ℕ) (z : ℂ) :
    Integrable (fun u : ℝ => (φ u : ℂ) * (u : ℂ) ^ n * Complex.exp (z * u)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((Complex.continuous_ofReal.comp φ.smooth.continuous).mul
      (Complex.continuous_ofReal.pow n)).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  · exact (φ.compactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right.mul_right

theorem complexKernelMoment_ofReal (φ : SmoothKernel) (n : ℕ) (β : ℝ) :
    complexKernelMoment φ n β = (kernelMoment φ n β : ℂ) := by
  simp only [complexKernelMoment, kernelMoment, ← Complex.ofReal_mul,
    ← Complex.ofReal_pow, ← Complex.ofReal_exp, integral_complex_ofReal]

theorem complexKernelTransform_ofReal (φ : SmoothKernel) (β : ℝ) :
    complexKernelTransform φ β = (kernelTransform φ β : ℂ) := by
  simpa [complexKernelTransform] using complexKernelMoment_ofReal φ 0 β

private theorem complexKernelMoment_bound_integrable (φ : SmoothKernel) (n : ℕ) (z : ℂ) :
    Integrable (fun u : ℝ => |φ u| * |u| ^ (n + 1) *
      Real.exp ((‖z‖ + 1) * |u|)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (φ.smooth.continuous.abs.mul (continuous_abs.pow (n + 1))).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
  · exact φ.compactSupport.abs.mul_right.mul_right

private theorem complexKernelMoment_deriv_bound (φ : SmoothKernel) (n : ℕ) (z w : ℂ) (u : ℝ)
    (hw : w ∈ Metric.ball z 1) :
    ‖(φ u : ℂ) * (u : ℂ) ^ (n + 1) * Complex.exp (w * u)‖ ≤
      |φ u| * |u| ^ (n + 1) * Real.exp ((‖z‖ + 1) * |u|) := by
  have hdist : ‖w - z‖ < 1 := by simpa [dist_eq_norm] using hw
  have hwNorm : ‖w‖ ≤ ‖z‖ + 1 := by
    have ht := norm_add_le (w - z) z
    rw [sub_add_cancel] at ht
    linarith
  have hwu : ‖w * (u : ℂ)‖ ≤ (‖z‖ + 1) * |u| := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hwNorm (abs_nonneg u)
  have hexp := (Complex.norm_exp_le_exp_norm (w * u)).trans (Real.exp_le_exp.mpr hwu)
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left hexp
      (mul_nonneg (abs_nonneg (φ u)) (pow_nonneg (abs_nonneg u) _))

theorem hasDerivAt_complexKernelMoment (φ : SmoothKernel) (n : ℕ) (z : ℂ) :
    HasDerivAt (complexKernelMoment φ n) (complexKernelMoment φ (n + 1) z) z := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w u => (φ u : ℂ) * (u : ℂ) ^ n * Complex.exp (w * u))
    (F' := fun w u => (φ u : ℂ) * (u : ℂ) ^ (n + 1) * Complex.exp (w * u))
    (bound := fun u : ℝ => |φ u| * |u| ^ (n + 1) * Real.exp ((‖z‖ + 1) * |u|))
    (s := Metric.ball z 1) (Metric.ball_mem_nhds z (by norm_num))
    (Filter.Eventually.of_forall fun w => (complexKernelMoment_integrable φ n w).aestronglyMeasurable)
    (complexKernelMoment_integrable φ n z)
    (complexKernelMoment_integrable φ (n + 1) z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u w hw => complexKernelMoment_deriv_bound φ n z w u hw)
    (complexKernelMoment_bound_integrable φ n z) ?_).2
  exact Filter.Eventually.of_forall fun u w _ => by
    convert (((Complex.hasDerivAt_exp (w * u)).comp w
      ((hasDerivAt_id w).mul_const (u : ℂ))).const_mul ((φ u : ℂ) * (u : ℂ) ^ n)) using 1 <;>
      simp [pow_succ]
    ring

theorem differentiable_complexKernelMoment (φ : SmoothKernel) (n : ℕ) :
    Differentiable ℂ (complexKernelMoment φ n) :=
  fun z => (hasDerivAt_complexKernelMoment φ n z).differentiableAt

theorem deriv_complexKernelMoment (φ : SmoothKernel) (n : ℕ) :
    deriv (complexKernelMoment φ n) = complexKernelMoment φ (n + 1) := by
  funext z
  exact (hasDerivAt_complexKernelMoment φ n z).deriv

theorem iteratedDeriv_complexKernelTransform (φ : SmoothKernel) (n : ℕ) :
    iteratedDeriv n (complexKernelTransform φ) = complexKernelMoment φ n := by
  induction n with
  | zero => rfl
  | succ n hn => rw [iteratedDeriv_succ, hn, deriv_complexKernelMoment]

theorem analyticAt_complexKernelTransform (φ : SmoothKernel) (z : ℂ) :
    AnalyticAt ℂ (complexKernelTransform φ) z :=
  (differentiable_complexKernelMoment φ 0).analyticAt z

theorem contDiff_complexKernelTransform (φ : SmoothKernel) :
    ContDiff ℂ ∞ (complexKernelTransform φ) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [iteratedDeriv_complexKernelTransform]
  exact differentiable_complexKernelMoment φ n

end BTZEntropy
