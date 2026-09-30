import FixedPointTheorems.brouwer
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.FunProp

/-!
# Correcting a continuous approximate moment map

The fixed point is applied to `z ↦ a + z - Q z`. A uniform approximation error
no larger than the ball radius makes this a self-map and yields `Q z = a`.
The vendored Brouwer proof is pinned and audited with its source provenance.
-/

namespace GapFamily.Quadrature

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A continuous approximate identity on a closed ball hits its centre exactly. -/
theorem exists_eq_center_of_error_le (a : V) {r : ℝ} (hr : 0 ≤ r)
    (Q : C(Metric.closedBall a r, V))
    (herror : ∀ z : Metric.closedBall a r, ‖Q z - (z : V)‖ ≤ r) :
    ∃ z : Metric.closedBall a r, Q z = a := by
  let F : C(Metric.closedBall a r, Metric.closedBall a r) :=
    ⟨fun z => ⟨a + (z : V) - Q z, by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have heq : a + (z : V) - Q z - a = (z : V) - Q z := by abel
      rw [heq, norm_sub_rev]
      exact herror z⟩, by fun_prop⟩
  obtain ⟨z, hz⟩ := brouwer_fixed_point (Metric.closedBall a r)
    (convex_closedBall a r) (isCompact_closedBall a r)
    ⟨a, Metric.mem_closedBall_self hr⟩ F
  refine ⟨z, ?_⟩
  have heq : a + (z : V) - Q z = (z : V) := congrArg Subtype.val hz
  have h : a + (z : V) = Q z + (z : V) :=
    (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)
  exact (add_right_cancel h).symm

end GapFamily.Quadrature
