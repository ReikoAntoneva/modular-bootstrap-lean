import GapFamily.Analytic.Kernel.FullKernelInputInverseColumn

/-! A physical output evaluation is a bounded linear functional of the
actual low-band input. Composing with the actual inverse input column gives
the holomorphic correction used by local repair. -/

noncomputable section

open Real

namespace GapFamily.Analytic

def correctedKernelResponseLinear {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    LowBandHilbert J B →ₗ[ℂ] ℂ where
  toFun f := correctedKernelResponse J B f j e
  map_add' f g := correctedKernelResponse_add J B hB f g j e he
  map_smul' c f := correctedKernelResponse_smul J B c f j e

def correctedKernelResponseFunctional {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    LowBandHilbert J B →L[ℂ] ℂ :=
  (correctedKernelResponseLinear J B hB j e he).mkContinuous
    (correctedKernelBound * (e * B + sqrt e * sqrt B) * sqrt (Fintype.card ι : ℝ))
    (fun f => norm_correctedKernelResponse_le J B hB f j e he)

@[simp] theorem correctedKernelResponseFunctional_apply {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e)
    (f : LowBandHilbert J B) :
    correctedKernelResponseFunctional J B hB j e he f = correctedKernelResponse J B f j e := rfl

theorem norm_correctedKernelResponseFunctional_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    ‖correctedKernelResponseFunctional J B hB j e he‖ ≤
      correctedKernelBound * (e * B + sqrt e * sqrt B) * sqrt (Fintype.card ι : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound
  · have := correctedKernelBound_pos
    have : 0 ≤ e := (abs_nonneg _).trans he
    positivity
  · exact fun f => norm_correctedKernelResponse_le J B hB f j e he

/-- The actual inverse-column correction is entire in the separate input
square-root coordinate, at every physical output point. -/
theorem differentiable_correctedKernelResponse_inverseColumn
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin j : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    Differentiable ℂ (fun z : ℂ =>
      correctedKernelResponse J B (correctedInputInverseColumn J B hB jin z) j e) :=
  (correctedKernelResponseFunctional J B hB j e he).differentiable.comp
    (differentiable_correctedInputInverseColumn J B hB jin)

end GapFamily.Analytic
