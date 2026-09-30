import GapFamily.Analytic.Modular.Geometry.ModularTruncatedCutoff

/-!
# Regular compact neighborhoods for upper-half-plane evaluation

An arbitrary compact upper-half-plane set lies in the interior of a larger
regular compact set. A smooth compact cutoff equals one on an open neighborhood
of that larger set. The original compact set needs no interior or regularity.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set UpperHalfPlane
open scoped ContDiff

/-- Every compact upper-half-plane set has a regular compact neighborhood,
itself contained in an open set with compact closure inside the upper half-plane. -/
theorem exists_regularCompact_upperNeighborhood {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ upperHalfPlaneSet) :
    ∃ L U : Set ℂ, IsCompact L ∧ closure (interior L) = L ∧
      K ⊆ interior L ∧ IsOpen U ∧ L ⊆ U ∧ IsCompact (closure U) ∧
      closure U ⊆ upperHalfPlaneSet := by
  obtain ⟨V, hV, hKV, hVH, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_upperHalfPlaneSet hKU
  obtain ⟨U, hU, hVU, hUH, hUc⟩ :=
    exists_open_between_and_isCompact_closure hVc isOpen_upperHalfPlaneSet hVH
  refine ⟨closure V, U, hVc, ?_, hKV.trans hV.subset_interior_closure,
    hU, hVU, hUc, hUH⟩
  exact subset_antisymm (closure_minimal interior_subset isClosed_closure)
    (closure_mono hV.subset_interior_closure)

/-- Actual regular compact enlargement and smooth plateau for every compact
upper-half-plane set, including sets with empty interior. -/
theorem exists_upperEvaluationCutoff {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ upperHalfPlaneSet) :
    ∃ (L U : Set ℂ) (χ : ℂ → ℂ),
      IsCompact L ∧ closure (interior L) = L ∧ K ⊆ interior L ∧
      IsOpen U ∧ L ⊆ U ∧ IsCompact (closure U) ∧ closure U ⊆ upperHalfPlaneSet ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ upperHalfPlaneSet ∧
      EqOn χ 1 U := by
  obtain ⟨L, U, hL, hLregular, hKL, hU, hLU, hUc, hUH⟩ :=
    exists_regularCompact_upperNeighborhood hK hKU
  obtain ⟨χ, hχ, hχc, hχH, hχone⟩ := exists_upperCutoff_eq_one hUc hUH
  exact ⟨L, U, χ, hL, hLregular, hKL, hU, hLU, hUc, hUH,
    hχ, hχc, hχH, hχone.mono subset_closure⟩

end GapFamily.Analytic.ModularGradient
