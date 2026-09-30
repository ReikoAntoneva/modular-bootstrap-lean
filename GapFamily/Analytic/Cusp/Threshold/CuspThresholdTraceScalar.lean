import GapFamily.Analytic.Cusp.Scalar.CuspConstantLocalResponse

/-! Actual scalar cancellation in the finite-height threshold trace. -/
noncomputable section
namespace GapFamily.Analytic.CuspThresholdTraceScalar
open Set MeasureTheory UpperHalfPlane

/-- The actual logarithmic constant-source profile at threshold. -/
theorem cuspConstantLogResponse_zero (t : ℝ) :
    cuspConstantLogResponse 0 t = 4 * (1 - Complex.exp (-(t : ℂ) / 2)) := by
  rw [cuspConstantLogResponse_eq_quotient (by norm_num) (by norm_num)]
  norm_num
  ring

/-- In logarithmic coordinates the decaying scalar term cancels exactly. -/
theorem cuspConstantLogResponse_zero_cancellation (t : ℝ) :
    Complex.exp (-(t : ℂ) / 2) + (1 / 4 : ℂ) * cuspConstantLogResponse 0 t = 1 := by
  rw [cuspConstantLogResponse_zero]
  ring

/-- The actual physical constant-source response is four times sqrt(y)-1 at zero. -/
theorem cuspConstantPhysicalResponse_zero {y : ℝ} (hy : 0 < y) :
    cuspConstantPhysicalResponse 0 y = 4 * ((Real.sqrt y : ℂ) - 1) := by
  rw [cuspConstantPhysicalResponse_eq_quotient (by norm_num) (by norm_num) hy]
  have hs : (y : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt y : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hy.le]
    norm_num
  norm_num only [sub_zero, zero_pow (by norm_num : 2 ≠ 0)]
  rw [hs]
  ring

/-- The true threshold scalar cancellation in positive physical height. -/
theorem cuspConstantPhysicalResponse_zero_cancellation {y : ℝ} (hy : 0 < y) :
    (1 : ℂ) + (1 / 4 : ℂ) * cuspConstantPhysicalResponse 0 y = (Real.sqrt y : ℂ) := by
  rw [cuspConstantPhysicalResponse_zero hy]
  ring

/-- Only the scalar portion of the finite-height trace, as an actual modular L2 vector. -/
def thresholdScalarTrace (L : ℝ) : ModularHilbert :=
  modularLowCut (Real.exp L) modularConstant + (1 / 4 : ℂ) • cuspConstantLocalResponse L 0

/-- The exact global representative includes the unchanged low part and the sharp cap. -/
theorem thresholdScalarTrace_ae {L : ℝ} (hL : 0 ≤ L) :
    thresholdScalarTrace L =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if τ.im ≤ Real.exp L then
        (if 1 < τ.im then (Real.sqrt τ.im : ℂ) else 1) else 0) := by
  filter_upwards [Lp.coeFn_add (modularLowCut (Real.exp L) modularConstant)
      ((1 / 4 : ℂ) • cuspConstantLocalResponse L 0),
    Lp.coeFn_smul (1 / 4 : ℂ) (cuspConstantLocalResponse L 0),
    modularLowCut_ae (Real.exp L) modularConstant, modularConstant_ae,
    cuspConstantLocalResponse_ae hL (by norm_num : (0 : ℂ) ≠ -(1 / 2 : ℂ))]
    with τ ha hs hl hq hc
  change (modularLowCut (Real.exp L) modularConstant +
    (1 / 4 : ℂ) • cuspConstantLocalResponse L 0) τ = _
  simp only [ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul, hl, Set.indicator_apply,
    Set.mem_ofPred_eq, hq, hc]
  by_cases hcap : τ.im ≤ Real.exp L
  · by_cases hy : 1 < τ.im
    · simp only [hcap, hy, and_self, ite_true]
      exact cuspConstantPhysicalResponse_zero_cancellation τ.im_pos
    · simp [hcap, hy]
  · simp [hcap]

/-- On the actual finite cusp strip this scalar contribution is exactly sqrt(height). -/
theorem thresholdScalarTrace_ae_cusp {L : ℝ} (hL : 0 ≤ L) :
    ∀ᵐ τ : UpperHalfPlane ∂modularMeasure, 1 < τ.im → τ.im ≤ Real.exp L →
      thresholdScalarTrace L τ = (Real.sqrt τ.im : ℂ) := by
  filter_upwards [thresholdScalarTrace_ae hL] with τ hτ
  intro hy hcap
  simpa only [hy, hcap, ite_true] using hτ

/-- The finite-height scalar contribution has an explicit actual Hilbert norm bound. -/
theorem norm_thresholdScalarTrace_le {L : ℝ} (hL : 0 ≤ L) :
    ‖thresholdScalarTrace L‖ ≤ Real.sqrt (Real.exp L) * ‖modularConstant‖ := by
  have hB : 1 ≤ Real.sqrt (Real.exp L) :=
    Real.one_le_sqrt.mpr (Real.one_le_exp_iff.mpr hL)
  calc
    ‖thresholdScalarTrace L‖ ≤ ‖(Real.sqrt (Real.exp L) : ℂ) • modularConstant‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [thresholdScalarTrace_ae hL,
        Lp.coeFn_smul (Real.sqrt (Real.exp L) : ℂ) modularConstant,
        modularConstant_ae] with τ ht hs hq
      simp only [ht, hs, Pi.smul_apply, smul_eq_mul, hq, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      split_ifs with hcap hy
      · simpa only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)] using Real.sqrt_le_sqrt hcap
      · simpa only [norm_one] using hB
      · simpa only [norm_zero] using Real.sqrt_nonneg (Real.exp L)
    _ = Real.sqrt (Real.exp L) * ‖modularConstant‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

end GapFamily.Analytic.CuspThresholdTraceScalar
