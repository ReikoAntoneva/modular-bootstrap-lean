import GapFamily.Analytic.Poincare.Continuation.PoincareComplementResidualValue
import GapFamily.Analytic.Poincare.Continuation.PoincareComplementEquation
import GapFamily.Analytic.Modular.ModularCoreLaplacianDomain
import GapFamily.Analytic.Cusp.Schur.CuspSchurGlobalPhysical

noncomputable section
namespace GapFamily.Analytic.PoincareComplement
open MeasureTheory ModularGradient CuspFourierCutoff CuspSchurLocal

/-- The original automorphic complementary Poincaré value belongs to the actual
Laplacian domain and has exactly the constructed unweighted shifted residual. -/
theorem exists_laplacian_residual (J : ℤ) {κ : ℂ}
    (hκ : (3 / 2 : ℝ) < κ.re) :
    ∃ hu : value (smoothCore J (exponent κ) (exponent_re_gt_two hκ)) ∈ laplacian.domain,
      laplacian ⟨value (smoothCore J (exponent κ) (exponent_re_gt_two hκ)), hu⟩ -
        parameter κ • value (smoothCore J (exponent κ) (exponent_re_gt_two hκ)) =
          cuspPoincareResidualSource J 0 (by norm_num) κ := by
  obtain ⟨hu, hA⟩ := PoincareGreen.exists_laplacian_value_of_core_weak
    (smoothCore J (exponent κ) (exponent_re_gt_two hκ))
    (laplacianSourceCore J (exponent κ) (exponent_re_gt_two hκ))
    (smoothCore_weak_equation J (exponent κ) (exponent_re_gt_two hκ))
  refine ⟨hu, ?_⟩
  rw [hA, laplacianSourceCore_value_exponent J hκ, add_sub_cancel_right]

/-- The actual Schur inverse of the complete residual is the original
convergent complementary Poincaré value, not a chosen weak-solution surrogate. -/
theorem actualSchurResolvent_residual_eq_value (J : ℤ) {κ : ℂ}
    (hκ : (3 / 2 : ℝ) < κ.re) :
    CuspSchur.actualSchurResolvent (parameter κ)
        (cuspPoincareResidualSource J 0 (by norm_num) κ) =
      value (smoothCore J (exponent κ) (exponent_re_gt_two hκ)) := by
  obtain ⟨hu, hA⟩ := exists_laplacian_residual J hκ
  have hp : 0 < κ.re := by linarith
  have hh : κ ≠ (1 / 2 : ℂ) := by
    intro he
    rw [he] at hκ
    norm_num at hκ
  have hR := CuspSchurGlobalPhysical.actualSchurResolvent_leftInverse_physical hp hh
    ⟨value (smoothCore J (exponent κ) (exponent_re_gt_two hκ)), hu⟩
  change CuspSchur.actualSchurResolvent (parameter κ)
    (laplacian ⟨value (smoothCore J (exponent κ) (exponent_re_gt_two hκ)), hu⟩ -
      parameter κ • value (smoothCore J (exponent κ) (exponent_re_gt_two hκ))) = _ at hR
  rw [hA] at hR
  exact hR

/-- The inverse's actual modular L² representative is the literal convergent
complementary cusp series. -/
theorem actualSchurResolvent_residual_ae_series (J : ℤ) {κ : ℂ}
    (hκ : (3 / 2 : ℝ) < κ.re) :
    CuspSchur.actualSchurResolvent (parameter κ)
        (cuspPoincareResidualSource J 0 (by norm_num) κ) =ᵐ[modularMeasure]
      series J (exponent κ) := by
  rw [actualSchurResolvent_residual_eq_value J hκ]
  exact smoothCore_value_ae J (exponent κ) (exponent_re_gt_two hκ)

end GapFamily.Analytic.PoincareComplement
