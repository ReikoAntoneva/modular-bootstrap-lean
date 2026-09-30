import GapFamily.Analytic.Kernel.FullKernel

/-!
# Holomorphic scalar rank-one extension

The energy coordinate is `|j| + b z²`, but the scalar rank-one factor is
defined using `sqrt b * z`. Agreement with the physical kernel is proved on
the nonnegative real axis only. No complex square-root identity is used.
-/

noncomputable section

namespace GapFamily.Analytic

open Real

/-- Holomorphic extension in the output square-root coordinate. -/
def correctedKernelHolOutput (j J : ℤ) (b E : ℝ) (z : ℂ) : ℂ :=
  fullKernelHol j J (|(j : ℝ)| + (b : ℂ) * z ^ 2) E +
    if j = 0 ∧ J = 0 then 12 * (sqrt b : ℂ) * z * (sqrt E : ℂ) else 0

/-- Holomorphic extension in the input square-root coordinate. -/
def correctedKernelHolInput (j J : ℤ) (b e : ℝ) (z : ℂ) : ℂ :=
  fullKernelHol j J e (|(J : ℝ)| + (b : ℂ) * z ^ 2) +
    if j = 0 ∧ J = 0 then 12 * (sqrt e : ℂ) * (sqrt b : ℂ) * z else 0

theorem differentiable_correctedKernelHolOutput (j J : ℤ) (b E : ℝ) :
    Differentiable ℂ (correctedKernelHolOutput j J b E) := by
  unfold correctedKernelHolOutput
  apply Differentiable.add
  · exact differentiable_fullKernelHol_comp j J _ _ (by fun_prop) (by fun_prop)
  · split_ifs <;> fun_prop

theorem differentiable_correctedKernelHolInput (j J : ℤ) (b e : ℝ) :
    Differentiable ℂ (correctedKernelHolInput j J b e) := by
  unfold correctedKernelHolInput
  apply Differentiable.add
  · exact differentiable_fullKernelHol_comp j J _ _ (by fun_prop) (by fun_prop)
  · split_ifs <;> fun_prop

theorem correctedKernelHolOutput_ofReal (j J : ℤ) (b E t : ℝ)
    (hb : 0 ≤ b) (ht : 0 ≤ t) :
    correctedKernelHolOutput j J b E t =
      correctedKernel j J (|(j : ℝ)| + b * t ^ 2) E := by
  unfold correctedKernelHolOutput correctedKernel scalarRankKernel
  push_cast
  congr 1
  by_cases h : j = 0 ∧ J = 0
  · rw [if_pos h, if_pos h]
    simp only [h.1, Int.cast_zero, abs_zero, zero_add]
    rw [sqrt_mul hb, sqrt_sq ht]
    push_cast
    ring
  · simp [h]

theorem correctedKernelHolInput_ofReal (j J : ℤ) (b e t : ℝ)
    (hb : 0 ≤ b) (ht : 0 ≤ t) :
    correctedKernelHolInput j J b e t =
      correctedKernel j J e (|(J : ℝ)| + b * t ^ 2) := by
  unfold correctedKernelHolInput correctedKernel scalarRankKernel
  push_cast
  congr 1
  by_cases h : j = 0 ∧ J = 0
  · rw [if_pos h, if_pos h]
    simp only [h.2, Int.cast_zero, abs_zero, zero_add]
    rw [sqrt_mul hb, sqrt_sq ht]
    push_cast
    ring
  · simp [h]

@[simp] theorem correctedKernelHolOutput_scalar_zero (J : ℤ) (b E : ℝ) :
    correctedKernelHolOutput 0 J b E 0 = 0 := by
  simp [correctedKernelHolOutput]

@[simp] theorem correctedKernelHolInput_scalar_zero (j : ℤ) (b e : ℝ) :
    correctedKernelHolInput j 0 b e 0 = 0 := by
  simp [correctedKernelHolInput]

end GapFamily.Analytic
