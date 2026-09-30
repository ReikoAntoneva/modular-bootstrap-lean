import GapFamily.Analytic.Poincare.PoincareHighCuspNormAnalytic

/-!
Entire high-cusp observations on actual compact complex-coordinate sets.
The pullback is through the literal upper-half-plane coordinate inclusion.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareHighCuspAnalytic

open Set UpperHalfPlane PoincareHighCusp

private theorem isCompact_highCuspUpperObservation (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) : IsCompact (UpperHalfPlane.coe ⁻¹' K) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  rw [Set.image_preimage_eq_of_subset (by simpa only [UpperHalfPlane.range_coe] using hKH)]
  exact isCompact_iff_compactSpace.mpr inferInstance

private def highCuspObservationMap (K : Set ℂ) (hKH : K ⊆ upperHalfPlaneSet) :
    C(K, UpperHalfPlane.coe ⁻¹' K) where
  toFun z := ⟨⟨z, hKH z.property⟩, z.property⟩
  continuous_toFun :=
    (continuous_subtype_val.upperHalfPlaneMk (fun z : K => hKH z.property)).subtype_mk _

/-- The literal high-cusp lift restricted to a compact set in complex coordinates. -/
def highCuspComplexOn (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (J : ℤ) (κ : ℂ) : C(K, ℂ) :=
  (continuedHighCuspOn (UpperHalfPlane.coe ⁻¹' K) J κ).comp (highCuspObservationMap K hKH)

@[simp] theorem highCuspComplexOn_apply (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (κ : ℂ) (z : K) :
    highCuspComplexOn K hKH J κ z = continuedHighCusp J κ (z : ℂ) := rfl

/-- Entire dependence in the actual uniform norm of the complex-coordinate target. -/
theorem differentiable_highCuspComplexOn (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) :
    Differentiable ℂ (highCuspComplexOn K hKH J) := by
  let : CompactSpace (UpperHalfPlane.coe ⁻¹' K) :=
    isCompact_iff_compactSpace.mp (isCompact_highCuspUpperObservation K hKH)
  change Differentiable ℂ (fun κ =>
    (ContinuousMap.compCLM ℂ ℂ (highCuspObservationMap K hKH))
      (continuedHighCuspOn (UpperHalfPlane.coe ⁻¹' K) J κ))
  exact (ContinuousMap.compCLM ℂ ℂ (highCuspObservationMap K hKH)).differentiable.comp
    (differentiable_continuedHighCuspOn (UpperHalfPlane.coe ⁻¹' K) J)

/-- Norm analyticity of the actual complex-coordinate restriction at every parameter. -/
theorem analyticAt_highCuspComplexOn (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (κ : ℂ) :
    AnalyticAt ℂ (highCuspComplexOn K hKH J) κ :=
  (differentiable_highCuspComplexOn K hKH J).analyticAt κ

/-- One compact-set constant works for every integer spin and the entire closed
radius-one-eighth parameter disk in the actual C(K) norm. -/
theorem exists_highCuspComplexOn_norm_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ 1 / 8 →
      ‖highCuspComplexOn K hKH J κ‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_compact_continuedHighCusp_bound
    (isCompact_highCuspUpperObservation K hKH)
  refine ⟨C, hC, fun J κ hκ => ?_⟩
  apply (ContinuousMap.norm_le _ hC.le).mpr
  intro z
  exact hb J κ hκ ⟨z, hKH z.property⟩ z.property

end GapFamily.Analytic.PoincareHighCuspAnalytic
