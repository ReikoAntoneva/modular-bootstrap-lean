import GapFamily.Analytic.Cusp.Profile.CuspWeightedSchurContinuation
import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedPhysical
import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurPhysical

noncomputable section
namespace GapFamily.Analytic.CuspSchurWeighted
open CuspSchurLocal

theorem localZeroTrace_eq_physical {α L T : ℝ} (hα : 0 < α)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T) {κ : ℂ} (hκ : 0 < κ.re)
    (F : ModularHilbert) :
    localZeroTrace α hα.le L T κ F = modularLowCut (Real.exp L)
      (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (parameter κ)
        (cuspWeightedInput α hα.le F)) +
       scalarCuspEmbedding (cuspScalarPencilSolution (parameter κ)
        (cuspWeightedInput α hα.le F))) := by
  change modularLowCut (Real.exp L) (constrainedResponse κ (cuspWeightedInput α hα.le F)) +
    cuspGreenWeightedLocalOutput α hα.le L T κ (cuspHalfLineSourceCoefficient F) = _
  rw [cuspGreenWeightedLocalOutput_eq_physical hα hL hT hLT hκ F, map_add]
  rfl

theorem localNumerator_eq_physical {α : ℝ} (hα : 0 ≤ α)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) (F : ModularHilbert) :
    localNumerator α hα κ F = inner ℂ modularConstant (cuspWeightedInput α hα F) +
      parameter κ *
        (inner ℂ modularConstant (meanZeroCuspEmbedding
          (cuspMeanZeroPencilSolution (parameter κ) (cuspWeightedInput α hα F))) +
         inner ℂ modularConstant (scalarCuspEmbedding
          (cuspScalarPencilSolution (parameter κ) (cuspWeightedInput α hα F)))) := by
  change inner ℂ modularConstant (cuspWeightedInput α hα F) + parameter κ *
    (inner ℂ modularConstant (constrainedResponse κ (cuspWeightedInput α hα F)) +
      cuspWeightedConstantPairingFunctional α κ F) = _
  rw [cuspWeightedConstantPairingFunctional_eq_physical hα hκ hp F]
  rfl

/-- The analytic weighted local Schur formula is the actual physical Schur
response of every weighted Hilbert source, with no source height bound. -/
theorem continuedLocalSchur_eq_physical {α L T : ℝ} (hα : 0 < α)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T) {κ : ℂ}
    (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) :
    continuedLocalSchur α hα.le L T κ =
      ((modularLowCut (Real.exp L)).comp
        (CuspSchur.actualSchurResolvent (parameter κ))).comp (cuspWeightedInput α hα.le) := by
  have hd : CuspSchur.actualSchurDenominator (parameter κ) =
      CuspSchur.continuedDenominator κ := CuspSchur.actualSchurDenominator_eq_continued hκ
  apply ContinuousLinearMap.ext
  intro F
  change localZeroTrace α hα.le L T κ F +
    ((CuspSchur.continuedDenominator κ)⁻¹ * localNumerator α hα.le κ F) •
      localTraceVector L κ =
    modularLowCut (Real.exp L)
      (CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le F))
  conv_rhs =>
    rw [actualSchurResolvent_expansion (parameter κ) (cuspWeightedInput α hα.le F)]
    rw [(modularLowCut (Real.exp L)).map_add, (modularLowCut (Real.exp L)).map_smul]
  rw [localZeroTrace_eq_physical hα hL hT hLT hκ F,
    localNumerator_eq_physical hα.le hκ hp F]
  conv_lhs =>
    arg 2
    arg 2
    rw [localTraceVector_eq_physical hL hκ]
  conv_rhs =>
    arg 2
    arg 1
    arg 2
    rw [hd]
  simp only [div_eq_mul_inv, mul_comm]

end GapFamily.Analytic.CuspSchurWeighted
