import GapFamily.Analytic.Modular.ModularGradientTest

/-!
# Closability of the actual modular gradient

The compact interior test identities hold on the graph and extend to its
closure by continuity. A vertical vector in the closed graph pairs to zero
with every scaled smooth test in both components, and hence vanishes.
This proves genuine closability without assuming ambient core density.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory
open scoped ContDiff

theorem frameTest_gradient_pairing_x (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior)
    (u : gradient.domain) :
    inner ℂ (frameTest φ hφ hc) (WithLp.ofLp (gradient u)).1 =
      inner ℂ (divergenceTest φ hφ hc 1) (u : ModularHilbert) := by
  rcases u with ⟨u, hu⟩
  change u ∈ value.range at hu
  obtain ⟨F, rfl⟩ := hu
  rw [gradient_apply_value, coreGradient_fst]
  exact frameTest_core_pairing φ hφ hc hs 1 _ F

theorem frameTest_gradient_pairing_y (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior)
    (u : gradient.domain) :
    inner ℂ (frameTest φ hφ hc) (WithLp.ofLp (gradient u)).2 =
      inner ℂ (divergenceTest φ hφ hc Complex.I) (u : ModularHilbert) := by
  rcases u with ⟨u, hu⟩
  change u ∈ value.range at hu
  obtain ⟨F, rfl⟩ := hu
  rw [gradient_apply_value, coreGradient_snd]
  exact frameTest_core_pairing φ hφ hc hs Complex.I _ F

/-- The actual weak horizontal identity persists on the topological graph closure. -/
theorem frameTest_graphClosure_pairing_x (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior)
    {p : ModularHilbert × GradientSpace} (hp : p ∈ gradient.graph.topologicalClosure) :
    inner ℂ (frameTest φ hφ hc) (WithLp.ofLp p.2).1 =
      inner ℂ (divergenceTest φ hφ hc 1) p.1 := by
  have hclosed : IsClosed {q : ModularHilbert × GradientSpace |
      inner ℂ (frameTest φ hφ hc) (WithLp.ofLp q.2).1 =
        inner ℂ (divergenceTest φ hφ hc 1) q.1} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  apply closure_minimal (t := {q : ModularHilbert × GradientSpace |
      inner ℂ (frameTest φ hφ hc) (WithLp.ofLp q.2).1 =
        inner ℂ (divergenceTest φ hφ hc 1) q.1}) ?_ hclosed hp
  intro q hq
  obtain ⟨u, rfl⟩ := (gradient.mem_graph_iff').mp hq
  exact frameTest_gradient_pairing_x φ hφ hc hs u

/-- The actual weak vertical identity persists on the topological graph closure. -/
theorem frameTest_graphClosure_pairing_y (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior)
    {p : ModularHilbert × GradientSpace} (hp : p ∈ gradient.graph.topologicalClosure) :
    inner ℂ (frameTest φ hφ hc) (WithLp.ofLp p.2).2 =
      inner ℂ (divergenceTest φ hφ hc Complex.I) p.1 := by
  have hclosed : IsClosed {q : ModularHilbert × GradientSpace |
      inner ℂ (frameTest φ hφ hc) (WithLp.ofLp q.2).2 =
        inner ℂ (divergenceTest φ hφ hc Complex.I) q.1} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  apply closure_minimal (t := {q : ModularHilbert × GradientSpace |
      inner ℂ (frameTest φ hφ hc) (WithLp.ofLp q.2).2 =
        inner ℂ (divergenceTest φ hφ hc Complex.I) q.1}) ?_ hclosed hp
  intro q hq
  obtain ⟨u, rfl⟩ := (gradient.mem_graph_iff').mp hq
  exact frameTest_gradient_pairing_y φ hφ hc hs u

theorem graphClosure_single_valued (p : ModularHilbert × GradientSpace)
    (hp : p ∈ gradient.graph.topologicalClosure) (hzero : p.1 = 0) : p.2 = 0 := by
  apply (WithLp.linearEquiv 2 ℂ (ModularHilbert × ModularHilbert)).injective
  change ((WithLp.ofLp p.2).1, (WithLp.ofLp p.2).2) = (0, 0)
  apply Prod.ext
  · apply frameTest_separates
    intro φ hφ hc hs
    simpa only [hzero, inner_zero_right] using frameTest_graphClosure_pairing_x φ hφ hc hs hp
  · apply frameTest_separates
    intro φ hφ hc hs
    simpa only [hzero, inner_zero_right] using frameTest_graphClosure_pairing_y φ hφ hc hs hp

/-- Closability is proved for the concrete smooth automorphic gradient. -/
theorem gradient_isClosable : gradient.IsClosable :=
  ⟨gradient.graph.topologicalClosure.toLinearPMap,
    (Submodule.toLinearPMap_graph_eq _ graphClosure_single_valued).symm⟩

/-- The closed gradient is the genuine graph closure of the actual operator. -/
def closedGradient : ModularHilbert →ₗ.[ℂ] GradientSpace := gradient.closure

theorem closedGradient_graph : closedGradient.graph = gradient.graph.topologicalClosure :=
  gradient_isClosable.graph_closure_eq_closure_graph.symm

theorem closedGradient_isClosed : closedGradient.IsClosed := gradient_isClosable.closure_isClosed

theorem gradient_le_closedGradient : gradient ≤ closedGradient := gradient.le_closure

theorem closedGradient_apply_value (F : smoothCore) :
    closedGradient ⟨value F, gradient_le_closedGradient.1 (LinearMap.mem_range_self value F)⟩ =
      coreGradient F := by
  exact (gradient_le_closedGradient.2 rfl).symm.trans (gradient_apply_value F)

theorem modularConstant_mem_closedGradient_domain : modularConstant ∈ closedGradient.domain :=
  gradient_le_closedGradient.1 modularConstant_mem_gradient_domain

theorem closedGradient_modularConstant :
    closedGradient ⟨modularConstant, modularConstant_mem_closedGradient_domain⟩ = 0 := by
  exact (gradient_le_closedGradient.2 rfl).symm.trans gradient_modularConstant

end GapFamily.Analytic.ModularGradient
