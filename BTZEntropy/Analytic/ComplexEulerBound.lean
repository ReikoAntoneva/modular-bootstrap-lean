import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Complex Euler product on the unit disc

The nonvanishing Euler product and its reciprocal square are holomorphic on
the open unit disc. Compact subdiscs give uniform bounds for the reciprocal
square used by the complex BTZ amplitude.
-/

noncomputable section

open scoped BigOperators Topology

namespace BTZEntropy

def complexEulerProduct (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (n + 1))

theorem complexEulerProduct_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    complexEulerProduct q ≠ 0 := by
  unfold complexEulerProduct
  simp only [sub_eq_add_neg]
  refine tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -q ^ (n + 1)) ?_ ?_
  · intro n
    have hpow : ‖q ^ (n + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    intro heq
    have hval : q ^ (n + 1) = 1 := by linear_combination -heq
    simp [hval] at hpow
  · simpa using (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (norm_nonneg q) hq)

theorem analyticAt_complexEulerProduct {q : ℂ} (hq : ‖q‖ < 1) :
    AnalyticAt ℂ complexEulerProduct q := by
  exact ModularForm.differentiableOn_tprod_one_sub_pow.analyticAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hq))

theorem analyticAt_complexEulerProduct_inv_sq {q : ℂ} (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (fun z => (complexEulerProduct z)⁻¹ ^ 2) q :=
  ((analyticAt_complexEulerProduct hq).inv (complexEulerProduct_ne_zero hq)).pow 2

theorem complexEulerProduct_inv_sq_bounded {r : ℝ} (hr : r < 1) :
    ∃ C > 0, ∀ q : ℂ, ‖q‖ ≤ r → ‖(complexEulerProduct q)⁻¹ ^ 2‖ ≤ C := by
  have hcont : ContinuousOn (fun q : ℂ => (complexEulerProduct q)⁻¹ ^ 2)
      (Metric.closedBall 0 r) := by
    intro q hq
    exact (analyticAt_complexEulerProduct_inv_sq
      (lt_of_le_of_lt (by simpa using hq) hr)).continuousAt.continuousWithinAt
  obtain ⟨C, hC, hbound⟩ :=
    ((isCompact_closedBall (0 : ℂ) r).image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun q hq => hbound _ ?_⟩
  exact ⟨q, by simpa using hq, rfl⟩

end BTZEntropy
