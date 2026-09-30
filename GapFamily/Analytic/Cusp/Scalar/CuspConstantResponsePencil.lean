import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseWeak
import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseFormPairing
import GapFamily.Analytic.Cusp.Scalar.CuspScalarPencilRegular

/-!
# The actual scalar pencil response to the modular constant

Physical uniqueness identifies the explicit finite-energy cusp response with
its genuine scalar pencil solution. The ordinary pairing of that constructed
form therefore evaluates the pencil response itself on `Re κ > 0`.
-/

noncomputable section
namespace GapFamily.Analytic

open ModularGradient

/-- The literal constant-source vector is the actual scalar pencil solution
on the physical parameter half-plane. -/
theorem cuspConstantScalarForm_eq_pencilSolution {κ : ℂ} (hκ : 0 < κ.re) :
    cuspConstantScalarForm hκ =
      cuspScalarPencilSolution (1 / 4 - κ ^ 2) modularConstant := by
  apply cuspScalarPencilSolution_unique_physical hκ modularConstant (cuspConstantScalarForm hκ)
  intro v
  simpa only [cuspScalarGradient, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    using cuspConstantScalarForm_test_weak hκ v

/-- The actual pencil constant pairing equals the convergent physical response
pairing; no continuation outside the physical half-plane is asserted. -/
theorem cuspScalarPencilSolution_constant_pairing {κ : ℂ} (hκ : 0 < κ.re) :
    inner ℂ modularConstant
        (scalarCuspEmbedding (cuspScalarPencilSolution (1 / 4 - κ ^ 2) modularConstant)) =
      1 / (κ + 1 / 2) ^ 2 := by
  rw [← cuspConstantScalarForm_eq_pencilSolution hκ]
  exact cuspConstantScalarForm_pairing hκ

/-- At zero spectral parameter, the actual scalar pencil constant pairing is one. -/
theorem cuspScalarPencilSolution_zero_constant_pairing :
    inner ℂ modularConstant (scalarCuspEmbedding (cuspScalarPencilSolution 0 modularConstant)) =
      1 := by
  have h := cuspScalarPencilSolution_constant_pairing (κ := (1 / 2 : ℂ)) (by norm_num)
  norm_num at h
  exact h

end GapFamily.Analytic
