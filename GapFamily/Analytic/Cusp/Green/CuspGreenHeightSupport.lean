import GapFamily.Analytic.Cusp.Green.CuspGreenScalarResponse
import GapFamily.Analytic.Cusp.Scalar.CuspScalarOrthogonal
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedIndicator

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory ModularGradient

/-- The literal height cutoff is symmetric for the actual modular L² inner product. -/
theorem modularHighCut_inner_symm (H : ℝ) (F G : ModularHilbert) :
    inner ℂ (modularHighCut H F) G = inner ℂ F (modularHighCut H G) := by
  rw [modularHighCut_apply, cuspZeroExtend_inner_restrict]
  have h := congrArg (starRingEnd ℂ)
    (cuspZeroExtend_inner_restrict H (cuspRestrict H G) F)
  simpa only [inner_conj_symm, modularHighCut_apply] using h.symm

/-- The low-height cutoff can be moved between factors without changing normalization. -/
theorem modularLowCut_inner_symm (H : ℝ) (F G : ModularHilbert) :
    inner ℂ (modularLowCut H F) G = inner ℂ F (modularLowCut H G) := by
  rw [modularLowCut_apply, modularLowCut_apply, inner_sub_left, inner_sub_right,
    modularHighCut_inner_symm]

/-- A literal upper height-support condition makes low cutoff invisible in every pairing. -/
theorem modularLowCut_inner_of_highCut_zero (H : ℝ) (F G : ModularHilbert)
    (hF : modularHighCut H F = 0) :
    inner ℂ (modularLowCut H G) F = inner ℂ G F := by
  rw [modularLowCut_inner_symm, modularLowCut_apply, hF, sub_zero]

/-- Compact support means an actual AE representative vanishes off a compact
set; no continuity or smoothness of the Hilbert source is assumed. -/
theorem exists_cuspGreen_source_height_of_compact (F : ModularHilbert)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hF : ∀ᵐ τ ∂modularMeasure, τ ∉ K → F τ = 0) :
    ∃ T : ℝ, 0 ≤ T ∧ modularHighCut (Real.exp T) F = 0 := by
  obtain ⟨B, hB⟩ := (hK.image UpperHalfPlane.continuous_im).bddAbove
  let T : ℝ := max 0 B
  have hT : 0 ≤ T := le_max_left _ _
  have hBT : B ≤ Real.exp T := by
    have hbT : B ≤ T := le_max_right _ _
    have he := Real.add_one_le_exp T
    linarith
  refine ⟨T, hT, ?_⟩
  apply Lp.ext
  filter_upwards [modularHighCut_ae (Real.exp T) F, hF,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := modularMeasure)] with τ hcut hf hzero
  rw [hcut, hzero]
  by_cases ht : Real.exp T < τ.im
  · rw [indicator_of_mem (show τ ∈ {τ : UpperHalfPlane | Real.exp T < τ.im} from ht)]
    exact hf (fun hk => (not_le_of_gt ht) ((hB ⟨τ, hk, rfl⟩).trans hBT))
  · exact indicator_of_notMem (show τ ∉ {τ : UpperHalfPlane | Real.exp T < τ.im} from ht) _

end GapFamily.Analytic
