import GapFamily.Analytic.Spatial.SpatialOrbitThresholdEvaluation

/-! Joint continuity of the canonical threshold kernel. -/
noncomputable section
namespace GapFamily.Analytic
open Set Filter UpperHalfPlane ModularGradient
open scoped Topology

namespace UpperWeightedCoherence

/-- Simultaneous variation of a weighted source and the upper observation point.
Compact coherence identifies the response with ordinary continuous evaluation
on a compact neighborhood of each observation point. -/
theorem continuous_weightedThresholdValue_comp
    {X : Type*} [TopologicalSpace X]
    (α : ℝ) (hα : 0 < α)
    {f : X → ModularHilbert} {τ : X → UpperHalfPlane}
    (hf : Continuous f) (hτ : Continuous τ) :
    Continuous (fun x => weightedThresholdValue α hα (f x) (τ x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨L, U, hL, _hreg, hτL, _hU, hLU, _hUc, hUH⟩ :=
    exists_regularCompact_upperNeighborhood
      (K := ({(τ x : ℂ)} : Set ℂ))
      isCompact_singleton (singleton_subset_upper (τ x))
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hLH : L ⊆ upperHalfPlaneSet := hLU.trans (subset_closure.trans hUH)
  let D := chosenEvaluation α hα L hLH
  let N : Set X := {y | (τ y : ℂ) ∈ L}
  have hLn : L ∈ 𝓝 (τ x : ℂ) :=
    mem_of_superset
      (isOpen_interior.mem_nhds (hτL (Set.mem_singleton _))) interior_subset
  have hN : N ∈ 𝓝 x :=
    (UpperHalfPlane.continuous_coe.comp hτ).continuousAt.eventually hLn
  have hc : ContinuousOn
      (fun y => weightedThresholdValue α hα (f y) (τ y)) N := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : N.domRestrict
        (fun y => weightedThresholdValue α hα (f y) (τ y)) =
        (fun y : N => D.family 0 (f y.1) ⟨(τ y.1 : ℂ), y.property⟩) := by
      funext y
      exact weightedThresholdValue_eq_evaluation hα D (f y.1) (τ y.1) y.property
    rw [heq]
    have hs : Continuous (fun y : N => D.family 0 (f y.1)) :=
      ((D.family 0).continuous.comp hf).comp continuous_subtype_val
    have hp : Continuous (fun y : N => (⟨(τ y.1 : ℂ), y.property⟩ : L)) :=
      ((UpperHalfPlane.continuous_coe.comp hτ).comp continuous_subtype_val).subtype_mk _
    exact hs.eval hp
  exact hc.continuousAt hN

end UpperWeightedCoherence

namespace SpatialPoint

/-- Joint continuity in both actual point arguments at the threshold. -/
theorem continuous_spatialThresholdKernel :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      spatialThresholdKernel p.1 p.2) :=
  UpperWeightedCoherence.continuous_weightedThresholdValue_comp (1 / 4) (by norm_num)
    ((continuous_spatialOrbitThresholdInput_source (1 / 2) (by norm_num)).comp continuous_snd)
    continuous_fst

theorem continuous_spatialThresholdCorrectedKernel :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      spatialThresholdCorrectedKernel p.1 p.2) :=
  continuous_spatialThresholdKernel.add continuous_const

end SpatialPoint
end GapFamily.Analytic
