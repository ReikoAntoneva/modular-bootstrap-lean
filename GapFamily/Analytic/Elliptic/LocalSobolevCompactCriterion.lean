import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith

/-!
# Compact approximation criterion

Uniform approximation by totally bounded sets supplies actual finite nets.
The analytic application must construct both the approximants and the error
bound; neither is inferred merely from naming a smoothing operation.
-/

namespace GapFamily.Analytic

open Set Metric

theorem totallyBounded_of_totallyBounded_approx {X : Type*} [PseudoMetricSpace X]
    {S : Set X}
    (h : ∀ ε : ℝ, 0 < ε → ∃ T : Set X, TotallyBounded T ∧
      ∀ x ∈ S, ∃ y ∈ T, dist x y < ε) : TotallyBounded S := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨T, hT, happ⟩ := h (ε / 2) (by positivity)
  obtain ⟨C, hC, hcover⟩ := Metric.totallyBounded_iff.mp hT (ε / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := happ x hx
  obtain ⟨c, hcb⟩ := Set.mem_iUnion.mp (hcover hy)
  obtain ⟨hc, hyc⟩ := Set.mem_iUnion.mp hcb
  refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, ?_⟩⟩
  have hyc' : dist y c < ε / 2 := hyc
  change dist x c < ε
  exact lt_of_le_of_lt (dist_triangle x y c) (by linarith)

end GapFamily.Analytic
