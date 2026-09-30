import GapFamily.Analytic.Cusp.Schur.CuspSchurOperator

/-!
# Literal ambient expansion of the actual Schur candidate

This is an identity of the defined totalized maps. It expands the two actual
subspace responses and the actual constant coordinate, without imposing pencil
regularity or a nonzero denominator.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal

open ModularGradient

theorem actualSchurResolvent_expansion (z : ℂ) (f : ModularHilbert) :
    CuspSchur.actualSchurResolvent z f =
      meanZeroCuspEmbedding (cuspMeanZeroPencilSolution z f) +
        scalarCuspEmbedding (cuspScalarPencilSolution z f) +
      ((inner ℂ modularConstant f + z *
          (inner ℂ modularConstant (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution z f)) +
            inner ℂ modularConstant (scalarCuspEmbedding (cuspScalarPencilSolution z f)))) /
          CuspSchur.actualSchurDenominator z) •
        (modularConstant + z •
          (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution z modularConstant) +
            scalarCuspEmbedding (cuspScalarPencilSolution z modularConstant))) := by
  simp only [CuspSchur.actualSchurResolvent_apply, CuspSchur.actualSchurSolution,
    CuspSchur.schurSolution_apply, CuspSchur.schurVector, CuspSchur.schurNumerator,
    CuspSchur.zeroTraceResponse_apply, map_add, map_smul,
    CuspSchur.constantForm, formEmbedding_coreForm, value_constantCore_one,
    inner_add_right, CuspSchur.actualSchurDenominator,
    meanZeroCuspEmbedding_apply, scalarCuspEmbedding_apply]

end GapFamily.Analytic.CuspSchurLocal
