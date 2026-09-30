import GapFamily.Analytic.Cusp.Schur.CuspSchurPhysical
import GapFamily.Analytic.Cusp.Scalar.CuspScalarHorizontalGradient

/-!
# Literal gradient expansion of the actual Schur candidate

These identities expand the genuine closed-gradient components of the defined
form-domain candidate. The constant form has zero gradient and the completed
scalar cusp space has zero horizontal gradient. No pencil unit, physical-region
condition, or nonzero-denominator premise is needed for this totalized algebra.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal
open ModularGradient

/-- The literal full gradient contains no constant-gradient term. -/
theorem actualSchurSolution_gradient_expansion (z : ℂ) (f : ModularHilbert) :
    formGradient (CuspSchur.actualSchurSolution z f) =
      formGradient (cuspMeanZeroPencilSolution z f : FormDomain) +
        formGradient (cuspScalarPencilSolution z f : FormDomain) +
      (CuspSchur.schurNumerator z (cuspScalarPencilSolution z) f /
        CuspSchur.actualSchurDenominator z) •
        (z • (formGradient (cuspMeanZeroPencilSolution z modularConstant : FormDomain) +
          formGradient (cuspScalarPencilSolution z modularConstant : FormDomain))) := by
  simp only [CuspSchur.actualSchurSolution, CuspSchur.schurSolution_apply,
    CuspSchur.schurVector, CuspSchur.zeroTraceResponse_apply, map_add, map_smul,
    CuspSchur.constantForm, formGradient_coreForm, coreGradient_constantCore,
    zero_add, CuspSchur.actualSchurDenominator]

/-- The actual horizontal channel comes entirely from the constrained response. -/
theorem actualSchurSolution_gradient_fst_expansion (z : ℂ) (f : ModularHilbert) :
    (formGradient (CuspSchur.actualSchurSolution z f)).ofLp.1 =
      (formGradient (cuspMeanZeroPencilSolution z f : FormDomain)).ofLp.1 +
      (CuspSchur.schurNumerator z (cuspScalarPencilSolution z) f /
        CuspSchur.actualSchurDenominator z) •
        (z • (formGradient
          (cuspMeanZeroPencilSolution z modularConstant : FormDomain)).ofLp.1) := by
  rw [actualSchurSolution_gradient_expansion]
  change (formGradient (cuspMeanZeroPencilSolution z f : FormDomain)).ofLp.1 +
      (formGradient (cuspScalarPencilSolution z f : FormDomain)).ofLp.1 +
      (CuspSchur.schurNumerator z (cuspScalarPencilSolution z) f /
        CuspSchur.actualSchurDenominator z) •
        (z • ((formGradient
            (cuspMeanZeroPencilSolution z modularConstant : FormDomain)).ofLp.1 +
          (formGradient
            (cuspScalarPencilSolution z modularConstant : FormDomain)).ofLp.1)) = _
  rw [cuspScalarForm_gradient_fst_eq_zero, cuspScalarForm_gradient_fst_eq_zero,
    add_zero, add_zero]

/-- The actual vertical channel retains both genuine subspace gradients. -/
theorem actualSchurSolution_gradient_snd_expansion (z : ℂ) (f : ModularHilbert) :
    (formGradient (CuspSchur.actualSchurSolution z f)).ofLp.2 =
      (formGradient (cuspMeanZeroPencilSolution z f : FormDomain)).ofLp.2 +
        (formGradient (cuspScalarPencilSolution z f : FormDomain)).ofLp.2 +
      (CuspSchur.schurNumerator z (cuspScalarPencilSolution z) f /
        CuspSchur.actualSchurDenominator z) •
        (z • ((formGradient
            (cuspMeanZeroPencilSolution z modularConstant : FormDomain)).ofLp.2 +
          (formGradient
            (cuspScalarPencilSolution z modularConstant : FormDomain)).ofLp.2)) := by
  rw [actualSchurSolution_gradient_expansion]
  rfl

end GapFamily.Analytic.CuspSchurLocal
