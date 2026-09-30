import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic

/-! Commutation with an invertible bounded operator passes to its inverse.
The commuting function need not be linear or continuous. -/

noncomputable section

namespace GapFamily.Analytic.InverseConjugation

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Any function commuting with an invertible operator commutes with its inverse. -/
theorem commutes_inverse_of_isUnit (P : H →L[ℂ] H) (C : H → H)
    (hcomm : ∀ f, C (P f) = P (C f)) (hunit : IsUnit P) (f : H) :
    C (Ring.inverse P f) = Ring.inverse P (C f) := by
  have hleft (g : H) : Ring.inverse P (P g) = g :=
    congrArg (fun Q : H →L[ℂ] H => Q g) (Ring.inverse_mul_cancel P hunit)
  have hright (g : H) : P (Ring.inverse P g) = g :=
    congrArg (fun Q : H →L[ℂ] H => Q g) (Ring.mul_inverse_cancel P hunit)
  calc
    C (Ring.inverse P f) = Ring.inverse P (P (C (Ring.inverse P f))) :=
      (hleft _).symm
    _ = Ring.inverse P (C (P (Ring.inverse P f))) := by rw [hcomm]
    _ = Ring.inverse P (C f) := by rw [hright]

/-- The inverse preserves the fixed points of every commuting function. -/
theorem inverse_preserves_fixed_point_of_isUnit (P : H →L[ℂ] H) (C : H → H)
    (hcomm : ∀ f, C (P f) = P (C f)) (hunit : IsUnit P)
    {f : H} (hf : C f = f) :
    C (Ring.inverse P f) = Ring.inverse P f := by
  rw [commutes_inverse_of_isUnit P C hcomm hunit, hf]

end GapFamily.Analytic.InverseConjugation
