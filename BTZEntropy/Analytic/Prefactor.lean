import BTZEntropy.Analytic.Amplitude
import BTZEntropy.Analytic.SaddlePhase

/-! The actual Gaussian prefactor and the constant entropy term. -/

noncomputable section

namespace BTZEntropy

/-- The positive Gaussian amplitude, before the universal `c^(-1/2)` factor. -/
def saddlePrefactor (φ : SmoothKernel) (x : ℝ) : ℝ :=
  amplitude φ (saddleBeta x) / Real.sqrt (2 * Real.pi * saddleHessian x)

theorem saddlePrefactor_pos (φ : SmoothKernel) {x : ℝ} (hx : 0 < x) :
    0 < saddlePrefactor φ x := by
  exact div_pos (amplitude_pos φ (saddleBeta_pos hx))
    (Real.sqrt_pos.2 (mul_pos (mul_pos (by norm_num) Real.pi_pos) (saddleHessian_pos hx)))

/-- The leading reference count with its actual one-dimensional Gaussian normalization. -/
def saddleCountScale (φ : SmoothKernel) (x c : ℝ) : ℝ :=
  Real.exp (leadingAction x c) * saddlePrefactor φ x / Real.sqrt c

theorem saddleCountScale_pos (φ : SmoothKernel) {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    0 < saddleCountScale φ x c :=
  div_pos (mul_pos (Real.exp_pos _) (saddlePrefactor_pos φ hx)) (Real.sqrt_pos.2 hc)

theorem log_saddlePrefactor (φ : SmoothKernel) {x : ℝ} (hx : 0 < x) :
    Real.log (saddlePrefactor φ x) = constantCoefficient φ x := by
  have hβ := saddleBeta_pos hx
  have hr := saddleRadius_pos hx
  have hh : 0 < 2 * Real.pi * saddleHessian x :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (saddleHessian_pos hx)
  have heq : 2 * Real.pi * saddleHessian x = saddleRadius x ^ 3 / 6 := by
    rw [saddleHessian_eq hx]
    field_simp
    ring
  rw [saddlePrefactor, Real.log_div (amplitude_ne_zero φ hβ) (Real.sqrt_pos.2 hh).ne',
    Real.log_sqrt hh.le, heq,
    Real.log_div (pow_pos hr 3).ne' (by norm_num : (6 : ℝ) ≠ 0), Real.log_pow]
  rw [amplitude, Real.log_mul (kernelTransform_pos φ _).ne'
    (boundaryGravitonFactor_pos (div_pos (by positivity) hβ)).ne']
  dsimp [constantCoefficient, dualSaddleBeta]
  ring

/-- Both the logarithmic coefficient and constant term follow from the actual
positive count scale, with no unspecified normalization constant. -/
theorem log_saddleCountScale (φ : SmoothKernel) {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Real.log (saddleCountScale φ x c) =
      leadingAction x c - (1 / 2 : ℝ) * Real.log c + constantCoefficient φ x := by
  rw [saddleCountScale,
    Real.log_div (mul_pos (Real.exp_pos _) (saddlePrefactor_pos φ hx)).ne'
      (Real.sqrt_pos.2 hc).ne',
    Real.log_mul (Real.exp_ne_zero _) (saddlePrefactor_pos φ hx).ne',
    Real.log_exp, log_saddlePrefactor φ hx, Real.log_sqrt hc.le]
  ring

theorem continuousAt_saddlePrefactor (φ : SmoothKernel) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (saddlePrefactor φ) x := by
  have hr : ContinuousAt saddleRadius x :=
    Real.continuous_sqrt.continuousAt.comp ((continuousAt_const.mul continuousAt_id))
  have hb : ContinuousAt saddleBeta x :=
    continuousAt_const.div hr (saddleRadius_pos hx).ne'
  have hh : ContinuousAt saddleHessian x :=
    continuousAt_const.div (hb.pow 3) (pow_pos (saddleBeta_pos hx) 3).ne'
  have hA : ContinuousAt (fun y => amplitude φ (saddleBeta y)) x :=
    (contDiffAt_amplitude φ (saddleBeta_pos hx)).continuousAt.comp hb
  exact hA.div
    (Real.continuous_sqrt.continuousAt.comp (continuousAt_const.mul hh))
    (Real.sqrt_pos.2 (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (saddleHessian_pos hx))).ne'

/-- Both sides of the Gaussian normalization are controlled on each compact
positive energy-ratio interval, with a strictly positive lower constant. -/
theorem saddlePrefactor_uniform_bounds (φ : SmoothKernel) {L U : ℝ}
    (hL : 0 < L) (hLU : L ≤ U) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ x ∈ Set.Icc L U, m ≤ saddlePrefactor φ x ∧ saddlePrefactor φ x ≤ M := by
  have hcont : ContinuousOn (saddlePrefactor φ) (Set.Icc L U) :=
    fun x hx => (continuousAt_saddlePrefactor φ (hL.trans_le hx.1)).continuousWithinAt
  obtain ⟨xm, hxm, hm⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hLU) hcont
  obtain ⟨xM, hxM, hM⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hLU) hcont
  exact ⟨saddlePrefactor φ xm, saddlePrefactor φ xM,
    saddlePrefactor_pos φ (hL.trans_le hxm.1),
    saddlePrefactor_pos φ (hL.trans_le hxM.1), fun x hx => ⟨hm hx, hM hx⟩⟩

end BTZEntropy
