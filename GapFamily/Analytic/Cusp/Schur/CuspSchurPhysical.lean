import GapFamily.Analytic.Cusp.Schur.CuspSchurAlgebra
import GapFamily.Analytic.Cusp.Scalar.CuspScalarPencilRegular

/-!
# The actual full-form Schur solution on the physical resolvent region

The constructed scalar pencil response discharges every scalar premise of the
Schur algebra. The bounded source map solves the full weak equation uniquely
for nonreal or negative-real parameters. Definitions are totalized elsewhere;
no inverse assertion is made on the nonnegative real axis.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchur
open ModularGradient

/-- The actual scalar response is regular on the complement of the nonnegative real ray. -/
theorem scalarPencil_isUnit_off_nonnegative_ray {z : ℂ}
    (hz : z.im ≠ 0 ∨ z.re < 0) : IsUnit (cuspScalarPencil z) := by
  apply cuspScalarPencil_isUnit_regular
  exact hz.elim Or.inl (fun h => Or.inr (lt_trans h (by norm_num)))

theorem meanZeroPencil_isUnit_off_nonnegative_ray {z : ℂ}
    (hz : z.im ≠ 0 ∨ z.re < 0) : IsUnit (cuspMeanZeroPencil z) :=
  hz.elim (cuspMeanZeroPencil_isUnit_of_im_ne_zero z)
    (fun h => cuspMeanZeroPencil_isUnit_of_re_nonpos z h.le)

/-- This identity uses the constructed scalar Riesz response and its actual inverse pencil. -/
theorem actualScalar_formPairing {z : ℂ} (hz : IsUnit (cuspScalarPencil z))
    (f : ModularHilbert) (w : cuspScalarForm) :
    formPairing z w (cuspScalarPencilSolution z f) = inner ℂ (formEmbedding w) f :=
  cuspScalarPencilSolution_equation hz f w

theorem actualScalar_formPairing_unique {z : ℂ} (hz : IsUnit (cuspScalarPencil z))
    (f : ModularHilbert) (u : cuspScalarForm)
    (hu : ∀ w : cuspScalarForm, formPairing z w u = inner ℂ (formEmbedding w) f) :
    u = cuspScalarPencilSolution z f :=
  cuspScalarPencilSolution_unique hz f u hu

/-- The literal denominator, now with both actual subspace responses. -/
def actualSchurDenominator (z : ℂ) : ℂ :=
  schurDenominator z (cuspScalarPencilSolution z)

theorem actualSchurDenominator_ne_zero {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0) :
    actualSchurDenominator z ≠ 0 :=
  schurDenominator_ne_zero_of_physical (meanZeroPencil_isUnit_off_nonnegative_ray hz)
    (cuspScalarPencilSolution z)
    (actualScalar_formPairing (scalarPencil_isUnit_off_nonnegative_ray hz)) hz

/-- The actual bounded full-form candidate, built from both genuine responses and the constant.
Its inverse identities are proved below off the nonnegative real ray. -/
def actualSchurSolution (z : ℂ) : ModularHilbert →L[ℂ] FormDomain :=
  schurSolution z (cuspScalarPencilSolution z)

/-- Ambient value of the totalized candidate; inverse identities require the regular-region hypothesis. -/
def actualSchurResolvent (z : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  formEmbedding.comp (actualSchurSolution z)

@[simp] theorem actualSchurResolvent_apply (z : ℂ) (f : ModularHilbert) :
    actualSchurResolvent z f = formEmbedding (actualSchurSolution z f) := rfl

/-- The full test-first weak equation has no unresolved scalar-response premise. -/
theorem actualSchurSolution_equation {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0)
    (f : ModularHilbert) (t : FormDomain) :
    inner ℂ (formGradient t) (formGradient (actualSchurSolution z f)) -
      z * inner ℂ (formEmbedding t) (actualSchurResolvent z f) =
      inner ℂ (formEmbedding t) f :=
  schurSolution_equation (meanZeroPencil_isUnit_off_nonnegative_ray hz)
    (cuspScalarPencilSolution z)
    (actualScalar_formPairing (scalarPencil_isUnit_off_nonnegative_ray hz))
    (actualSchurDenominator_ne_zero hz) f t

/-- Uniqueness is in the actual full completed modular form domain. -/
theorem actualSchurSolution_unique {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0)
    (f : ModularHilbert) (u : FormDomain)
    (hu : ∀ t : FormDomain, inner ℂ (formGradient t) (formGradient u) -
      z * inner ℂ (formEmbedding t) (formEmbedding u) = inner ℂ (formEmbedding t) f) :
    u = actualSchurSolution z f :=
  schurSolution_unique (meanZeroPencil_isUnit_off_nonnegative_ray hz)
    (cuspScalarPencilSolution z)
    (actualScalar_formPairing_unique (scalarPencil_isUnit_off_nonnegative_ray hz))
    (actualSchurDenominator_ne_zero hz) f u hu

theorem existsUnique_actual_full_weak (z : ℂ) (hz : z.im ≠ 0 ∨ z.re < 0)
    (f : ModularHilbert) :
    ∃! u : FormDomain, ∀ t : FormDomain,
      inner ℂ (formGradient t) (formGradient u) -
        z * inner ℂ (formEmbedding t) (formEmbedding u) = inner ℂ (formEmbedding t) f := by
  refine ⟨actualSchurSolution z f, actualSchurSolution_equation hz f, ?_⟩
  exact fun u hu => actualSchurSolution_unique hz f u hu

/-- The literal trace coefficient of the constructed actual solution. -/
theorem actualSchurSolution_trace (z : ℂ) (f : ModularHilbert) :
    cuspAverageTrace (actualSchurSolution z f) =
      schurNumerator z (cuspScalarPencilSolution z) f / actualSchurDenominator z := by
  rw [actualSchurSolution, schurSolution_apply, schurVector_trace]
  rfl

end GapFamily.Analytic.CuspSchur
