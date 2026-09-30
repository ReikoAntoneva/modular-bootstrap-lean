import GapFamily.Analytic.Poincare.Continuation.PoincareCommonRegionResolvent
import GapFamily.Analytic.Modular.Elliptic.ModularUpperCoreEvaluation
import GapFamily.Analytic.Poincare.PoincareHighCuspSplit

noncomputable section
namespace GapFamily.Analytic.PoincareComplement
open Set MeasureTheory ModularGradient CuspFourierCutoff CuspSchurLocal UpperHalfPlane Dirichlet
open scoped ContDiff

/-- The actual resolvent's continuous graph representative, plus the genuine
high-cusp lift, recovers the original convergent Poincaré series pointwise on
every compact upper chart, including seams and thin observation sets. -/
theorem exists_actualSchur_evaluation_add_highCusp_eq_series
    (J : ℤ) {κ : ℂ} (hκ : (3 / 2 : ℝ) < κ.re)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (K : Set ℂ) [CompactSpace K] (hKU : K ⊆ U) :
    ∃ hu : CuspSchur.actualSchurResolvent (parameter κ)
        (cuspPoincareResidualSource J 0 (by norm_num) κ) ∈ laplacian.domain,
      ∀ z : K,
        laplacianUpperCompactEvaluation χ hχ hcχ hsχ U hU hχU K hKU z
            (gradientLift laplacian ⟨CuspSchur.actualSchurResolvent (parameter κ)
              (cuspPoincareResidualSource J 0 (by norm_num) κ), hu⟩) +
          PoincareHighCusp.continuedHighCusp J κ z =
            complexPoincareSeries 0 J (exponent κ) (ofComplex z) := by
  rw [actualSchurResolvent_residual_eq_value J hκ]
  obtain ⟨hu, _hA⟩ := exists_laplacian_residual J hκ
  refine ⟨hu, ?_⟩
  intro z
  rw [laplacianUpperCompactEvaluation_core χ hχ hcχ hsχ U hU hχU K hKU z]
  have hz : 0 < (z : ℂ).im := by
    apply hsχ
    apply subset_tsupport χ
    rw [Function.mem_support, hχU (hKU z.property)]
    exact one_ne_zero
  let τ : UpperHalfPlane := ⟨z, hz⟩
  change series J (exponent κ) (ofComplex (τ : ℂ)) +
    PoincareHighCusp.continuedHighCusp J κ (τ : ℂ) =
      complexPoincareSeries 0 J (exponent κ) (ofComplex (τ : ℂ))
  rw [ofComplex_apply]
  exact (PoincareHighCusp.complexPoincareSeries_eq_complement_add_continuedHighCusp J
    (by have := exponent_re_gt_two hκ; linarith) τ).symm

end GapFamily.Analytic.PoincareComplement
