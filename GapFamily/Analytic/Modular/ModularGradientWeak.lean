import GapFamily.Analytic.Modular.ModularGradientClosed

/-!
# Weak derivative and constant channel of the closed modular gradient

The concrete graph closure satisfies the ordinary compact interior test
identities. Removing the actual average preserves its domain and gradient.
These statements need neither a dense-domain premise nor a spectral gap.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory
open scoped ContDiff

theorem frameTest_closedGradient_pairing_x (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior)
    (u : closedGradient.domain) :
    inner ℂ (frameTest φ hφ hc) (WithLp.ofLp (closedGradient u)).1 =
      inner ℂ (divergenceTest φ hφ hc 1) (u : ModularHilbert) := by
  apply frameTest_graphClosure_pairing_x φ hφ hc hs
    (p := ((u : ModularHilbert), closedGradient u))
  rw [← closedGradient_graph]
  exact (closedGradient.mem_graph_iff').mpr ⟨u, rfl⟩

theorem frameTest_closedGradient_pairing_y (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior)
    (u : closedGradient.domain) :
    inner ℂ (frameTest φ hφ hc) (WithLp.ofLp (closedGradient u)).2 =
      inner ℂ (divergenceTest φ hφ hc Complex.I) (u : ModularHilbert) := by
  apply frameTest_graphClosure_pairing_y φ hφ hc hs
    (p := ((u : ModularHilbert), closedGradient u))
  rw [← closedGradient_graph]
  exact (closedGradient.mem_graph_iff').mpr ⟨u, rfl⟩

theorem constantProjection_mem_closedGradient_domain (f : ModularHilbert) :
    modularConstantProjection f ∈ closedGradient.domain := by
  rw [modularConstantProjection_apply]
  exact closedGradient.domain.smul_mem _ modularConstant_mem_closedGradient_domain

theorem closedGradient_constantProjection (f : ModularHilbert) :
    closedGradient ⟨modularConstantProjection f,
      constantProjection_mem_closedGradient_domain f⟩ = 0 := by
  have hsub : (⟨modularConstantProjection f,
      constantProjection_mem_closedGradient_domain f⟩ : closedGradient.domain) =
      modularAverage f • ⟨modularConstant, modularConstant_mem_closedGradient_domain⟩ :=
    Subtype.ext (modularConstantProjection_apply f)
  rw [hsub, LinearPMap.map_smul, closedGradient_modularConstant, smul_zero]

theorem meanZeroProjection_mem_closedGradient_domain (u : closedGradient.domain) :
    modularMeanZeroProjection u ∈ closedGradient.domain := by
  rw [modularMeanZeroProjection_eq]
  exact closedGradient.domain.sub_mem u.property
    (constantProjection_mem_closedGradient_domain u)

theorem closedGradient_meanZeroProjection (u : closedGradient.domain) :
    closedGradient ⟨modularMeanZeroProjection u,
      meanZeroProjection_mem_closedGradient_domain u⟩ = closedGradient u := by
  have hsub : (⟨modularMeanZeroProjection u,
      meanZeroProjection_mem_closedGradient_domain u⟩ : closedGradient.domain) =
      u - ⟨modularConstantProjection u, constantProjection_mem_closedGradient_domain u⟩ := by
    apply Subtype.ext
    simp only [modularMeanZeroProjection_eq, sub_apply,
      ContinuousLinearMap.id_apply, Submodule.coe_sub]
  rw [hsub, LinearPMap.map_sub, closedGradient_constantProjection, sub_zero]

/-- Subtracting the ordinary modular average does not change the actual energy. -/
theorem closedGradient_meanZeroProjection_norm (u : closedGradient.domain) :
    ‖closedGradient ⟨modularMeanZeroProjection u,
      meanZeroProjection_mem_closedGradient_domain u⟩‖ = ‖closedGradient u‖ := by
  rw [closedGradient_meanZeroProjection]

theorem constantSpace_le_closedGradient_kernel :
    modularConstantSpace ≤ closedGradient.ker := by
  apply Submodule.span_le.mpr
  intro f hf
  obtain rfl := Set.mem_singleton_iff.mp hf
  exact LinearPMap.mem_ker_iff.mpr
    ⟨⟨modularConstant, modularConstant_mem_closedGradient_domain⟩, rfl,
      closedGradient_modularConstant⟩

end GapFamily.Analytic.ModularGradient
