import GapFamily.Analytic.Cusp.Green.CuspGreenTailObserved
import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedTail
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual weighted Green tail on an observed collar

The separated tail is a genuine rank-one operator from ordinary half-line L²
to continuous functions on the observed collar. Its parameter dependence is
analytic in operator norm across zero for a positive source weight.
-/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory CuspHalfLineLaplace CuspHalfLineLaplaceTail
open scoped Topology

/-- The separated actual Green tail with exponential source weight. -/
def cuspGreenWeightedTailOperator (α L T : ℝ) (κ : ℂ) :
    HalfLineL2 →L[ℂ] C(CuspGreenCollar 0 L, ℂ) :=
  (tailLaplace T ((α : ℂ) + κ)).smulRight (cuspGreenTailObserved L κ)

@[simp] theorem cuspGreenWeightedTailOperator_apply (α L T : ℝ) (κ : ℂ)
    (f : HalfLineL2) (t : CuspGreenCollar 0 L) :
    cuspGreenWeightedTailOperator α L T κ f t =
      cuspGreenTailValue t κ * tailLaplace T ((α : ℂ) + κ) f := by
  change tailLaplace T ((α : ℂ) + κ) f * cuspGreenTailObserved L κ t = _
  rw [cuspGreenTailObserved_apply, mul_comm]

/-- The bounded operator equals the literal weighted Green tail for every source. -/
theorem cuspGreenWeightedTailOperator_apply_integral {α L T : ℝ}
    (hT : 0 ≤ T) (hLT : L ≤ T) {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re)
    (f : HalfLineL2) (t : CuspGreenCollar 0 L) :
    cuspGreenWeightedTailOperator α L T κ f t =
      ∫ u : ℝ in Ioi T,
        cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u := by
  rw [cuspGreenWeightedTailOperator_apply]
  exact (cuspGreen_weighted_tail_integral hT (t.property.2.trans hLT) hβ f).symm

/-- Analyticity holds in the norm of bounded operators with continuous outputs. -/
theorem analyticAt_cuspGreenWeightedTailOperator (α L T : ℝ) {κ : ℂ}
    (hβ : 0 < ((α : ℂ) + κ).re) :
    AnalyticAt ℂ (cuspGreenWeightedTailOperator α L T) κ := by
  have hf : AnalyticAt ℂ (fun z : ℂ => tailLaplace T ((α : ℂ) + z)) κ :=
    (tailLaplace_analyticAt T hβ).comp_of_eq (analyticAt_const.add analyticAt_id) rfl
  have hg := analyticAt_cuspGreenTailObserved L κ
  have hb := ContinuousLinearMap.analyticAt_bilinear (𝕜 := ℂ)
    (E := HalfLineL2 →L[ℂ] ℂ) (F := C(CuspGreenCollar 0 L, ℂ))
    (G := HalfLineL2 →L[ℂ] C(CuspGreenCollar 0 L, ℂ))
    (ContinuousLinearMap.smulRightL ℂ HalfLineL2 C(CuspGreenCollar 0 L, ℂ))
    (tailLaplace T ((α : ℂ) + κ), cuspGreenTailObserved L κ)
  exact hb.comp_of_eq (hf.prod hg) rfl

theorem analyticAt_cuspGreenWeightedTailOperator_zero {α : ℝ} (hα : 0 < α) (L T : ℝ) :
    AnalyticAt ℂ (cuspGreenWeightedTailOperator α L T) 0 :=
  analyticAt_cuspGreenWeightedTailOperator α L T (by simpa using hα)

theorem analyticOnNhd_cuspGreenWeightedTailOperator (α L T : ℝ) :
    AnalyticOnNhd ℂ (cuspGreenWeightedTailOperator α L T) {κ : ℂ | -α < κ.re} := by
  intro κ hκ
  change -α < κ.re at hκ
  apply analyticAt_cuspGreenWeightedTailOperator α L T
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith

theorem cuspGreenWeightedTailOperator_norm_le {α L T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) :
    ‖cuspGreenWeightedTailOperator α L T κ‖ ≤
      ‖cuspGreenTailObserved L κ‖ *
        (Real.exp (-((α : ℂ) + κ).re * T) / Real.sqrt (2 * ((α : ℂ) + κ).re)) := by
  rw [cuspGreenWeightedTailOperator, ContinuousLinearMap.norm_smulRight_apply, mul_comm]
  exact mul_le_mul_of_nonneg_left (tailLaplace_norm_le hT hβ) (norm_nonneg _)

/-- One constant controls the observed tail on a full closed parameter disk,
uniformly in the source cutoff height. -/
theorem cuspGreenWeightedTailOperator_uniform_bound {α : ℝ} (hα : 0 < α) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ κ : ℂ, ‖κ‖ ≤ α / 2 →
      ‖cuspGreenWeightedTailOperator α L T κ‖ ≤ C * Real.exp (-(α / 2) * T) := by
  obtain ⟨C, hC, hbound⟩ :=
    ((isCompact_closedBall (0 : ℂ) (α / 2)).image
      (differentiable_cuspGreenTailObserved L).continuous).isBounded.exists_pos_norm_le
  refine ⟨C / Real.sqrt α, by positivity, ?_⟩
  intro T hT κ hκ
  have hv : ‖cuspGreenTailObserved L κ‖ ≤ C := by
    apply hbound
    exact ⟨κ, by simpa only [Metric.mem_closedBall, dist_zero_right] using hκ, rfl⟩
  rw [cuspGreenWeightedTailOperator, ContinuousLinearMap.norm_smulRight_apply]
  calc
    ‖tailLaplace T ((α : ℂ) + κ)‖ * ‖cuspGreenTailObserved L κ‖ ≤
        (Real.exp (-(α / 2) * T) / Real.sqrt α) * C := by
      exact mul_le_mul (tailLaplace_norm_le_uniform hα hT hκ) hv
        (norm_nonneg _) (by positivity)
    _ = (C / Real.sqrt α) * Real.exp (-(α / 2) * T) := by ring

end GapFamily.Analytic
