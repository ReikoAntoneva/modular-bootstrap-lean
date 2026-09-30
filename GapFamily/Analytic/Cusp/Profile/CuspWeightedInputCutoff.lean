import GapFamily.Analytic.Cusp.Profile.CuspWeightedInput
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedIndicator

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory
open scoped Topology

/-- Exponential weights make actual source truncation small in operator norm. -/
theorem cuspWeightedInput_highCut_norm_le (α : ℝ) (hα : 0 ≤ α) (T : ℝ) :
    ‖(modularHighCut (Real.exp T)).comp (cuspWeightedInput α hα)‖ ≤
      Real.exp (-α * T) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [modularHighCut_ae (Real.exp T) (cuspWeightedInput α hα f),
    cuspWeightedInput_ae α hα f] with τ hcut hf
  change ‖modularHighCut (Real.exp T) (cuspWeightedInput α hα f) τ‖ ≤ _
  rw [hcut]
  by_cases hy : Real.exp T < τ.im
  · rw [indicator_of_mem (show τ ∈ {τ : UpperHalfPlane | Real.exp T < τ.im} from hy), hf,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg τ.im_pos.le _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ (Real.exp T) ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos T) hy.le (neg_nonpos.mpr hα)
      _ = Real.exp (-α * T) := by rw [← Real.exp_mul]; congr 1; ring
  · rw [indicator_of_notMem (show τ ∉ {τ : UpperHalfPlane | Real.exp T < τ.im} from hy),
      norm_zero]
    positivity

theorem cuspWeightedInput_lowCut_error_norm_le (α : ℝ) (hα : 0 ≤ α) (T : ℝ) :
    ‖(modularLowCut (Real.exp T)).comp (cuspWeightedInput α hα) -
      cuspWeightedInput α hα‖ ≤ Real.exp (-α * T) := by
  have heq : (modularLowCut (Real.exp T)).comp (cuspWeightedInput α hα) -
      cuspWeightedInput α hα =
      -((modularHighCut (Real.exp T)).comp (cuspWeightedInput α hα)) := by
    apply ContinuousLinearMap.ext
    intro f
    change modularLowCut (Real.exp T) (cuspWeightedInput α hα f) -
      cuspWeightedInput α hα f = -modularHighCut (Real.exp T) (cuspWeightedInput α hα f)
    rw [modularLowCut_apply]
    abel
  rw [heq, norm_neg]
  exact cuspWeightedInput_highCut_norm_le α hα T

/-- The finite-height weighted inputs converge to the actual noncompact input
uniformly over the Hilbert unit ball. -/
theorem cuspWeightedInput_lowCut_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (fun T : ℝ => (modularLowCut (Real.exp T)).comp (cuspWeightedInput α hα.le))
      atTop (𝓝 (cuspWeightedInput α hα.le)) := by
  have he : Tendsto (fun T : ℝ => Real.exp (-α * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hα))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun T => norm_nonneg _)
    (cuspWeightedInput_lowCut_error_norm_le α hα.le) he

end GapFamily.Analytic
