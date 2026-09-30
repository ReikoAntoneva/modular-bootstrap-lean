import GapFamily.Analytic.Cusp.Green.CuspGreenTailFrame
import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedTail
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# The actual weighted vertical-frame tail operator

The shifted derivative tail is a rank-one bounded operator from the genuine
half-line `L²` space to continuous functions on the observation collar. The
same operator has a literal ordinarily convergent Green derivative integral
and is analytic across the threshold with a positive source weight.
-/

noncomputable section
namespace GapFamily.Analytic

open Set Filter MeasureTheory CuspHalfLineLaplace CuspHalfLineLaplaceTail
open scoped Topology

/-- Ordinary integrability of the literal shifted left-derivative tail. -/
theorem cuspGreenFrame_weighted_integrableOn_tail {t T α : ℝ}
    (hT : 0 ≤ T) (htT : t ≤ T) {κ : ℂ}
    (hβ : 0 < ((α : ℂ) + κ).re) (f : HalfLineL2) :
    IntegrableOn (fun u : ℝ =>
      (cuspGreenLeftSlope 0 t u κ + (1 / 2 : ℂ) * cuspGreen 0 t u κ) *
        Complex.exp (-(α : ℂ) * u) * f u) (Ioi T) := by
  apply ((tailLaplace_integrable hT hβ f).const_mul (cuspGreenTailFrameValue t κ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [cuspGreenLeftSlope_add_half_mul_weight_eq_tailFrame t u α (htT.trans hu.le) κ]
  ring

/-- Ordinary integrability also holds with the original spatial derivative,
rather than its explicit left-slope formula. -/
theorem cuspGreenFrame_weighted_deriv_integrableOn_tail {t T α : ℝ}
    (hT : 0 ≤ T) (htT : t ≤ T) {κ : ℂ}
    (hβ : 0 < ((α : ℂ) + κ).re) (f : HalfLineL2) :
    IntegrableOn (fun u : ℝ =>
      (deriv (fun v : ℝ => cuspGreen 0 v u κ) t + (1 / 2 : ℂ) * cuspGreen 0 t u κ) *
        Complex.exp (-(α : ℂ) * u) * f u) (Ioi T) := by
  apply (cuspGreenFrame_weighted_integrableOn_tail hT htT hβ f).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [(cuspGreen_hasDerivAt_left 0 t u (htT.trans_lt hu) κ).deriv]

/-- The ordinary derivative tail equals the genuine half-line Laplace functional. -/
theorem cuspGreenFrame_weighted_tail_integral {t T α : ℝ}
    (hT : 0 ≤ T) (htT : t ≤ T) {κ : ℂ}
    (hβ : 0 < ((α : ℂ) + κ).re) (f : HalfLineL2) :
    (∫ u : ℝ in Ioi T,
      (cuspGreenLeftSlope 0 t u κ + (1 / 2 : ℂ) * cuspGreen 0 t u κ) *
        Complex.exp (-(α : ℂ) * u) * f u) =
      cuspGreenTailFrameValue t κ * tailLaplace T ((α : ℂ) + κ) f := by
  rw [tailLaplace_apply hT hβ, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [cuspGreenLeftSlope_add_half_mul_weight_eq_tailFrame t u α (htT.trans hu.le) κ]
  ring

/-- The actual exponentially weighted vertical-frame tail with continuous output. -/
def cuspGreenWeightedTailFrameOperator (α L T : ℝ) (κ : ℂ) :
    HalfLineL2 →L[ℂ] C(CuspGreenCollar 0 L, ℂ) :=
  (tailLaplace T ((α : ℂ) + κ)).smulRight (cuspGreenTailFrameObserved L κ)

@[simp] theorem cuspGreenWeightedTailFrameOperator_apply (α L T : ℝ) (κ : ℂ)
    (f : HalfLineL2) (t : CuspGreenCollar 0 L) :
    cuspGreenWeightedTailFrameOperator α L T κ f t =
      cuspGreenTailFrameValue t κ * tailLaplace T ((α : ℂ) + κ) f := by
  change tailLaplace T ((α : ℂ) + κ) f * cuspGreenTailFrameObserved L κ t = _
  rw [cuspGreenTailFrameObserved_apply, mul_comm]

theorem cuspGreenWeightedTailFrameOperator_apply_integral {α L T : ℝ}
    (hT : 0 ≤ T) (hLT : L ≤ T) {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re)
    (f : HalfLineL2) (t : CuspGreenCollar 0 L) :
    cuspGreenWeightedTailFrameOperator α L T κ f t =
      ∫ u : ℝ in Ioi T,
        (cuspGreenLeftSlope 0 t u κ + (1 / 2 : ℂ) * cuspGreen 0 t u κ) *
          Complex.exp (-(α : ℂ) * u) * f u := by
  rw [cuspGreenWeightedTailFrameOperator_apply]
  exact (cuspGreenFrame_weighted_tail_integral hT (t.property.2.trans hLT) hβ f).symm

/-- The operator is the integral of the actual derivative in the observation
coordinate; the tail stays strictly above every observation point. -/
theorem cuspGreenWeightedTailFrameOperator_apply_deriv_integral {α L T : ℝ}
    (hT : 0 ≤ T) (hLT : L ≤ T) {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re)
    (f : HalfLineL2) (t : CuspGreenCollar 0 L) :
    cuspGreenWeightedTailFrameOperator α L T κ f t =
      ∫ u : ℝ in Ioi T,
        (deriv (fun v : ℝ => cuspGreen 0 v u κ) t + (1 / 2 : ℂ) * cuspGreen 0 t u κ) *
          Complex.exp (-(α : ℂ) * u) * f u := by
  rw [cuspGreenWeightedTailFrameOperator_apply_integral hT hLT hβ]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [(cuspGreen_hasDerivAt_left 0 t u ((t.property.2.trans hLT).trans_lt hu) κ).deriv]

/-- Analyticity is in the actual bounded-operator norm. -/
theorem analyticAt_cuspGreenWeightedTailFrameOperator (α L T : ℝ) {κ : ℂ}
    (hβ : 0 < ((α : ℂ) + κ).re) :
    AnalyticAt ℂ (cuspGreenWeightedTailFrameOperator α L T) κ := by
  have hf : AnalyticAt ℂ (fun z : ℂ => tailLaplace T ((α : ℂ) + z)) κ :=
    (tailLaplace_analyticAt T hβ).comp_of_eq (analyticAt_const.add analyticAt_id) rfl
  have hg := analyticAt_cuspGreenTailFrameObserved L κ
  have hb := ContinuousLinearMap.analyticAt_bilinear (𝕜 := ℂ)
    (E := HalfLineL2 →L[ℂ] ℂ) (F := C(CuspGreenCollar 0 L, ℂ))
    (G := HalfLineL2 →L[ℂ] C(CuspGreenCollar 0 L, ℂ))
    (ContinuousLinearMap.smulRightL ℂ HalfLineL2 C(CuspGreenCollar 0 L, ℂ))
    (tailLaplace T ((α : ℂ) + κ), cuspGreenTailFrameObserved L κ)
  exact hb.comp_of_eq (hf.prod hg) rfl

theorem analyticAt_cuspGreenWeightedTailFrameOperator_zero {α : ℝ}
    (hα : 0 < α) (L T : ℝ) :
    AnalyticAt ℂ (cuspGreenWeightedTailFrameOperator α L T) 0 :=
  analyticAt_cuspGreenWeightedTailFrameOperator α L T (by simpa using hα)

theorem analyticOnNhd_cuspGreenWeightedTailFrameOperator (α L T : ℝ) :
    AnalyticOnNhd ℂ (cuspGreenWeightedTailFrameOperator α L T)
      {κ : ℂ | -α < κ.re} := by
  intro κ hκ
  change -α < κ.re at hκ
  apply analyticAt_cuspGreenWeightedTailFrameOperator α L T
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith

theorem cuspGreenWeightedTailFrameOperator_norm_le {α L T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) :
    ‖cuspGreenWeightedTailFrameOperator α L T κ‖ ≤
      ‖cuspGreenTailFrameObserved L κ‖ *
        (Real.exp (-((α : ℂ) + κ).re * T) / Real.sqrt (2 * ((α : ℂ) + κ).re)) := by
  rw [cuspGreenWeightedTailFrameOperator, ContinuousLinearMap.norm_smulRight_apply, mul_comm]
  exact mul_le_mul_of_nonneg_left (tailLaplace_norm_le hT hβ) (norm_nonneg _)

/-- Uniform exponential decay on a full closed parameter disk around threshold. -/
theorem cuspGreenWeightedTailFrameOperator_uniform_bound {α : ℝ}
    (hα : 0 < α) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ κ : ℂ, ‖κ‖ ≤ α / 2 →
      ‖cuspGreenWeightedTailFrameOperator α L T κ‖ ≤ C * Real.exp (-(α / 2) * T) := by
  obtain ⟨C, hC, hbound⟩ :=
    ((isCompact_closedBall (0 : ℂ) (α / 2)).image
      (differentiable_cuspGreenTailFrameObserved L).continuous).isBounded.exists_pos_norm_le
  refine ⟨C / Real.sqrt α, by positivity, ?_⟩
  intro T hT κ hκ
  have hv : ‖cuspGreenTailFrameObserved L κ‖ ≤ C := by
    apply hbound
    exact ⟨κ, by simpa only [Metric.mem_closedBall, dist_zero_right] using hκ, rfl⟩
  rw [cuspGreenWeightedTailFrameOperator, ContinuousLinearMap.norm_smulRight_apply]
  calc
    ‖tailLaplace T ((α : ℂ) + κ)‖ * ‖cuspGreenTailFrameObserved L κ‖ ≤
        (Real.exp (-(α / 2) * T) / Real.sqrt α) * C := by
      exact mul_le_mul (tailLaplace_norm_le_uniform hα hT hκ) hv
        (norm_nonneg _) (by positivity)
    _ = (C / Real.sqrt α) * Real.exp (-(α / 2) * T) := by ring

/-- At each point of the shifted half-plane the tail vanishes in operator norm
as the source truncation height tends to infinity. -/
theorem cuspGreenWeightedTailFrameOperator_tendsto (α L : ℝ) {κ : ℂ}
    (hβ : 0 < ((α : ℂ) + κ).re) :
    Tendsto (fun T : ℝ => cuspGreenWeightedTailFrameOperator α L T κ) atTop (𝓝 0) := by
  have he : Tendsto (fun T : ℝ => Real.exp (-((α : ℂ) + κ).re * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hβ))
  have hb := (he.div_const (Real.sqrt (2 * ((α : ℂ) + κ).re))).const_mul
    ‖cuspGreenTailFrameObserved L κ‖
  simp only [zero_div, mul_zero] at hb
  apply (tendsto_zero_iff_norm_tendsto_zero
    (f := fun T : ℝ => cuspGreenWeightedTailFrameOperator α L T κ)).mpr
  exact squeeze_zero' (Filter.Eventually.of_forall fun T => norm_nonneg _)
    ((eventually_ge_atTop (0 : ℝ)).mono fun T hT =>
      cuspGreenWeightedTailFrameOperator_norm_le hT hβ) hb

end GapFamily.Analytic
