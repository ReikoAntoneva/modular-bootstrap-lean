import BTZEntropy.Coefficient
import BTZEntropy.Observable
import BTZEntropy.Analytic.DeterminantRegularity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Analytic property of the smoothing amplitude

Compact support makes every exponentially weighted kernel moment integrable.
Differentiation with respect to inverse temperature inserts one energy factor.
All bounds below are proved from the actual kernel; no regularity or positivity
assumption about its transform is added.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace BTZEntropy

/-- Exponentially weighted moments give all derivatives of the kernel transform. -/
def kernelMoment (φ : SmoothKernel) (n : ℕ) (β : ℝ) : ℝ :=
  ∫ u : ℝ, φ u * u ^ n * Real.exp (β * u)

theorem kernelMoment_integrable (φ : SmoothKernel) (n : ℕ) (β : ℝ) :
    Integrable (fun u : ℝ => φ u * u ^ n * Real.exp (β * u)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (φ.smooth.continuous.mul (continuous_id.pow n)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  · exact φ.compactSupport.mul_right.mul_right

@[simp] theorem kernelMoment_zero (φ : SmoothKernel) :
    kernelMoment φ 0 = kernelTransform φ := by
  funext β
  simp [kernelMoment, kernelTransform]

theorem kernelTransform_pos (φ : SmoothKernel) (β : ℝ) :
    0 < kernelTransform φ β := by
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    have hzero : (φ : ℝ → ℝ) = fun _ => 0 := by
      funext u
      exact not_not.mp fun hu => h ⟨u, hu⟩
    have := φ.normalized
    simp only [hzero, integral_zero] at this
    norm_num at this
  apply integral_pos_of_integrable_nonneg_nonzero
    (φ.smooth.continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  · change Integrable (fun u : ℝ => φ u * Real.exp (β * u))
    simpa using kernelMoment_integrable φ 0 β
  · exact fun u => mul_nonneg (φ.nonneg u) (Real.exp_pos _).le
  · exact mul_ne_zero hu (Real.exp_ne_zero _)

private theorem kernelMoment_bound_integrable (φ : SmoothKernel) (n : ℕ) (β : ℝ) :
    Integrable (fun u : ℝ => |φ u| * |u| ^ (n + 1) *
      Real.exp ((|β| + 1) * |u|)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (φ.smooth.continuous.abs.mul (continuous_abs.pow (n + 1))).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
  · exact φ.compactSupport.abs.mul_right.mul_right

private theorem kernelMoment_deriv_bound (φ : SmoothKernel) (n : ℕ) (β x u : ℝ)
    (hx : x ∈ Metric.ball β 1) :
    ‖φ u * u ^ (n + 1) * Real.exp (x * u)‖ ≤
      |φ u| * |u| ^ (n + 1) * Real.exp ((|β| + 1) * |u|) := by
  have hdist : |x - β| < 1 := by simpa [Real.dist_eq] using hx
  have hxabs : |x| ≤ |β| + 1 := by
    have ht := norm_add_le (x - β) β
    simp only [sub_add_cancel, Real.norm_eq_abs] at ht
    linarith
  have hxu : x * u ≤ (|β| + 1) * |u| :=
    (le_abs_self (x * u)).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hxabs (abs_nonneg _))
  simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)] using
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxu)
      (mul_nonneg (abs_nonneg (φ u)) (pow_nonneg (abs_nonneg u) _))

theorem hasDerivAt_kernelMoment (φ : SmoothKernel) (n : ℕ) (β : ℝ) :
    HasDerivAt (kernelMoment φ n) (kernelMoment φ (n + 1) β) β := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u : ℝ => φ u * u ^ n * Real.exp (x * u))
    (F' := fun x u : ℝ => φ u * u ^ (n + 1) * Real.exp (x * u))
    (bound := fun u : ℝ => |φ u| * |u| ^ (n + 1) * Real.exp ((|β| + 1) * |u|))
    (s := Metric.ball β 1) (Metric.ball_mem_nhds β (by norm_num))
    (Filter.Eventually.of_forall fun x => (kernelMoment_integrable φ n x).aestronglyMeasurable)
    (kernelMoment_integrable φ n β)
    (kernelMoment_integrable φ (n + 1) β).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u x hx => kernelMoment_deriv_bound φ n β x u hx)
    (kernelMoment_bound_integrable φ n β) ?_).2
  exact Filter.Eventually.of_forall fun u x _ => by
    convert (((Real.hasDerivAt_exp (x * u)).comp x
      ((hasDerivAt_id x).mul_const u)).const_mul (φ u * u ^ n)) using 1 <;>
      simp [pow_succ]
    ring

theorem differentiable_kernelMoment (φ : SmoothKernel) (n : ℕ) :
    Differentiable ℝ (kernelMoment φ n) :=
  fun β => (hasDerivAt_kernelMoment φ n β).differentiableAt

theorem deriv_kernelMoment (φ : SmoothKernel) (n : ℕ) :
    deriv (kernelMoment φ n) = kernelMoment φ (n + 1) := by
  funext β
  exact (hasDerivAt_kernelMoment φ n β).deriv

theorem iteratedDeriv_kernelTransform (φ : SmoothKernel) (n : ℕ) :
    iteratedDeriv n (kernelTransform φ) = kernelMoment φ n := by
  induction n with
  | zero => simp
  | succ n hn => rw [iteratedDeriv_succ, hn, deriv_kernelMoment]

theorem contDiff_kernelTransform (φ : SmoothKernel) :
    ContDiff ℝ ∞ (kernelTransform φ) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [iteratedDeriv_kernelTransform]
  exact differentiable_kernelMoment φ n

theorem amplitude_pos (φ : SmoothKernel) {β : ℝ} (hβ : 0 < β) :
    0 < amplitude φ β := by
  apply mul_pos (kernelTransform_pos φ β)
  apply boundaryGravitonFactor_pos
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)) hβ

theorem amplitude_ne_zero (φ : SmoothKernel) {β : ℝ} (hβ : 0 < β) :
    amplitude φ β ≠ 0 := ne_of_gt (amplitude_pos φ hβ)

theorem contDiffAt_amplitude (φ : SmoothKernel) {β : ℝ} (hβ : 0 < β) :
    ContDiffAt ℝ ∞ (amplitude φ) β := by
  have hdual : 0 < 4 * Real.pi ^ 2 / β :=
    div_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)) hβ
  have harg : ContDiffAt ℝ ∞ (fun x : ℝ => 4 * Real.pi ^ 2 / x) β :=
    contDiffAt_const.div contDiffAt_id (ne_of_gt hβ)
  exact (contDiff_kernelTransform φ).contDiffAt.mul
    ((contDiffAt_boundaryGravitonFactor hdual).comp β harg)

theorem contDiffOn_amplitude (φ : SmoothKernel) :
    ContDiffOn ℝ ∞ (amplitude φ) (Set.Ioi 0) :=
  fun _ hβ => (contDiffAt_amplitude φ hβ).contDiffWithinAt

theorem contDiffOn_logAmplitude (φ : SmoothKernel) :
    ContDiffOn ℝ ∞ (fun β => Real.log (amplitude φ β)) (Set.Ioi 0) :=
  fun _ hβ => ((contDiffAt_amplitude φ hβ).log
    (amplitude_ne_zero φ hβ)).contDiffWithinAt

/-- The first coefficient for every actual smooth kernel, with the amplitude
nonvanishing condition discharged by the analytic positivity theorem. -/
theorem entropyCoefficient_one_smoothKernel (φ : SmoothKernel) {energyRatio : ℝ}
    (h : 0 < energyRatio) :
    entropyCoefficient φ energyRatio 1 = firstEntropyCoefficient φ energyRatio :=
  entropyCoefficient_one φ h (amplitude_ne_zero φ (saddleBeta_pos h))

end BTZEntropy
