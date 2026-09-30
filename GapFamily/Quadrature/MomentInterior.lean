import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Interior membership from functional margins

These separation lemmas isolate the convex-geometric step in prescribed-count
quadrature. The margin may depend on the functional, so it can be instantiated
with polynomial variation rather than an ambient Euclidean norm.
-/

open Set

namespace GapFamily.Quadrature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point belongs to the interior of a convex set if every nonzero continuous
linear functional takes a strictly larger value somewhere in the set. -/
theorem mem_interior_of_functional_margin {s : Set E} {x : E}
    (hs : Convex ℝ s) (hi : (interior s).Nonempty)
    (hm : ∀ f : StrongDual ℝ E, f ≠ 0 → ∃ y ∈ s, f x < f y) :
    x ∈ interior s := by
  by_contra hx
  obtain ⟨f, hf, hsupport⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hs hx hi
  obtain ⟨y, hy, hxy⟩ := hm f hf
  exact hxy.not_ge (hsupport y hy)

/-- A functional margin at `a` absorbs any perturbation whose value under each
functional is bounded by that margin. -/
theorem mem_interior_of_functional_margin_of_le {s : Set E} {a x : E}
    {margin : StrongDual ℝ E → ℝ}
    (hs : Convex ℝ s) (hi : (interior s).Nonempty)
    (hm : ∀ f : StrongDual ℝ E, f ≠ 0 →
      ∃ y ∈ s, f a + margin f < f y)
    (hx : ∀ f : StrongDual ℝ E, f ≠ 0 → f (x - a) ≤ margin f) :
    x ∈ interior s := by
  apply mem_interior_of_functional_margin hs hi
  intro f hf
  obtain ⟨y, hy, hfy⟩ := hm f hf
  refine ⟨y, hy, lt_of_le_of_lt ?_ hfy⟩
  have hfx := hx f hf
  rw [map_sub] at hfx
  exact (sub_le_iff_le_add.mp hfx).trans_eq (add_comm _ _)

/-- A strict uniform margin measured in the operator norm places the entire
closed ball inside the convex set's interior. -/
theorem closedBall_subset_interior_of_functional_margin {s : Set E} {a : E} {r : ℝ}
    (hs : Convex ℝ s) (hi : (interior s).Nonempty)
    (hm : ∀ f : StrongDual ℝ E, f ≠ 0 →
      ∃ y ∈ s, f a + ‖f‖ * r < f y) :
    Metric.closedBall a r ⊆ interior s := by
  intro x hx
  apply mem_interior_of_functional_margin_of_le hs hi hm
  intro f _
  have hnorm : ‖x - a‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using f.le_opNorm_of_le hnorm)

end GapFamily.Quadrature
