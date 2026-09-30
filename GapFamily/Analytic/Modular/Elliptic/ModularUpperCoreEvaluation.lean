import GapFamily.Analytic.Modular.Elliptic.ModularUpperCompactEvaluation

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set Filter MeasureTheory Dirichlet UpperHalfPlane
open scoped ContDiff

/-- On a genuine smooth-core operator-domain value, the actual upper graph
evaluation is exactly the original function, even on a thin compact set. -/
theorem laplacianUpperCompactEvaluation_core
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) (z : K)
    (F : smoothCore) (hu : value F ∈ laplacian.domain) :
    laplacianUpperCompactEvaluation χ hχ hcχ hsχ U hU hχU K hKU z
      (gradientLift laplacian ⟨value F, hu⟩) = F.val z := by
  have hUH : U ⊆ upperHalfPlaneSet := by
    intro w hw
    apply hsχ
    apply subset_tsupport χ
    rw [Function.mem_support, hχU hw]
    exact one_ne_zero
  apply laplacianUpperCompactEvaluation_eq_localRepresentative χ hχ hcχ hsχ U hU hχU
    K hKU z (gradientLift laplacian ⟨value F, hu⟩) hU (hKU z.property) Subset.rfl
    (F.property.1.continuousOn.mono hUH)
  have hv := upperCutoffHilbertValueOperator_value_ae χ hχ hcχ hsχ F
  filter_upwards [ae_restrict_of_ae hv, ae_restrict_mem hU.measurableSet] with w hw hwU
  simp only [laplacianUpperGraphValue, ContinuousLinearMap.comp_apply, gradientEmbedding_lift]
  rw [hw, hχU hwU, one_mul]

end GapFamily.Analytic.ModularGradient
