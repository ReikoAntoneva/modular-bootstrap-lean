import GapFamily.Analytic.Cusp.Schur.CuspSchurPhysical
import GapFamily.Analytic.Cusp.Schur.CuspSchurOperatorBridge

/-!
# Both inverse identities for the actual physical Schur map

Off the nonnegative real axis the constructed Schur value lies in the true
modular Laplacian domain and is a left and right inverse of A-z. At z=-1 it
agrees with the original shifted Riesz solution. No threshold continuation or
form-valued continuation through the continuous spectrum is asserted.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchur
open ModularGradient

/-- The actual Schur value belongs to the true full modular operator domain. -/
theorem actualSchurResolvent_mem_laplacian_domain {z : ℂ}
    (hz : z.im ≠ 0 ∨ z.re < 0) (f : ModularHilbert) :
    actualSchurResolvent z f ∈ laplacian.domain :=
  formEmbedding_mem_laplacian_domain_of_formPairing z (actualSchurSolution z f) f
    (actualSchurSolution_equation hz f)

/-- The ambient Schur map is a right inverse of the actual shifted modular Laplacian. -/
theorem actualSchurResolvent_rightInverse {z : ℂ}
    (hz : z.im ≠ 0 ∨ z.re < 0) (f : ModularHilbert) :
    laplacian ⟨actualSchurResolvent z f, actualSchurResolvent_mem_laplacian_domain hz f⟩ -
      z • actualSchurResolvent z f = f :=
  laplacian_sub_smul_of_formPairing z (actualSchurSolution z f) f
    (actualSchurSolution_equation hz f)

/-- The same actual bounded map is a left inverse on the full operator domain. -/
theorem actualSchurResolvent_leftInverse {z : ℂ}
    (hz : z.im ≠ 0 ∨ z.re < 0) (x : laplacian.domain) :
    actualSchurResolvent z (laplacian x - z • (x : ModularHilbert)) = x := by
  have h := actualSchurSolution_unique hz (laplacian x - z • (x : ModularHilbert))
    (formLift ⟨x, laplacian_domain_le x.property⟩) (formPairing_laplacian z x)
  exact (congrArg formEmbedding h).symm

/-- At the mass-shift parameter the constructed Schur source map is the original Riesz map. -/
theorem actualSchurSolution_neg_one : actualSchurSolution (-1) = weakSolution := by
  apply ContinuousLinearMap.ext
  intro f
  have h := eq_weakSolution_of_formPairing (-1) (actualSchurSolution (-1) f) f
    (actualSchurSolution_equation (z := -1) (Or.inr (by norm_num)) f)
  simpa only [neg_add_cancel, zero_smul, add_zero] using h

/-- This checks the literal shifted inverse normalization in the ambient Hilbert space. -/
theorem actualSchurResolvent_neg_one : actualSchurResolvent (-1) = weakResolvent := by
  apply ContinuousLinearMap.ext
  intro f
  rw [actualSchurResolvent_apply, actualSchurSolution_neg_one, weakResolvent_apply]

end GapFamily.Analytic.CuspSchur
