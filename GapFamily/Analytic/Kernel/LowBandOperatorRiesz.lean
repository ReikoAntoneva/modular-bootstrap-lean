import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Riesz representation of bounded kernel forms

These constructions use the supplied sesquilinear form itself. The representing operator is
obtained from Hilbert-space duality; it is not additional input data.
-/

noncomputable section

open scoped InnerProductSpace

namespace GapFamily.Analytic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Algebraic sesquilinear packaging of a concrete two-variable function. -/
def algebraicSesquilinearForm (B : H → H → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ c x y, B (c • x) y = star c * B x y)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₂ : ∀ c x y, B x (c • y) = c * B x y) :
    H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := B x
      map_add' := hadd₂ x
      map_smul' := fun c y => hsmul₂ c x y }
  map_add' x y := by
    ext z
    exact hadd₁ x y z
  map_smul' c x := by
    ext y
    exact hsmul₁ c x y

/-- The continuous sesquilinear form associated to a concrete function and its proved bound. -/
def boundedSesquilinearForm (B : H → H → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ c x y, B (c • x) y = star c * B x y)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₂ : ∀ c x y, B x (c • y) = c * B x y)
    (M : ℝ) (hbound : ∀ x y, ‖B x y‖ ≤ M * ‖x‖ * ‖y‖) :
    H →L⋆[ℂ] H →L[ℂ] ℂ :=
  (algebraicSesquilinearForm B hadd₁ hsmul₁ hadd₂ hsmul₂).mkContinuous₂ M hbound

@[simp]
theorem boundedSesquilinearForm_apply (B : H → H → ℂ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ c x y, B (c • x) y = star c * B x y)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₂ : ∀ c x y, B x (c • y) = c * B x y)
    (M : ℝ) (hbound : ∀ x y, ‖B x y‖ ≤ M * ‖x‖ * ‖y‖) (x y : H) :
    boundedSesquilinearForm B hadd₁ hsmul₁ hadd₂ hsmul₂ M hbound x y = B x y := rfl

variable [CompleteSpace H]

/-- The operator representing a bounded form in the second inner-product slot. -/
def sesquilinearOperator (B : H →L⋆[ℂ] H →L[ℂ] ℂ) : H →L[ℂ] H :=
  (InnerProductSpace.continuousLinearMapOfBilin B).adjoint

@[simp]
theorem inner_sesquilinearOperator (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (x y : H) :
    inner ℂ x (sesquilinearOperator B y) = B x y := by
  rw [sesquilinearOperator, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]

/-- The representing operator inherits the form's operator-norm bound. -/
theorem norm_sesquilinearOperator_le (B : H →L⋆[ℂ] H →L[ℂ] ℂ) :
    ‖sesquilinearOperator B‖ ≤ ‖B‖ := by
  rw [sesquilinearOperator, LinearIsometryEquiv.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun x => ?_
  change ‖(InnerProductSpace.toDual ℂ H).symm (B x)‖ ≤ ‖B‖ * ‖x‖
  rw [LinearIsometryEquiv.norm_map]
  exact B.le_opNorm x

/-- A pointwise two-variable bound is sufficient for the operator bound. -/
theorem norm_sesquilinearOperator_le_of_bound (B : H →L⋆[ℂ] H →L[ℂ] ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x y, ‖B x y‖ ≤ M * ‖x‖ * ‖y‖) :
    ‖sesquilinearOperator B‖ ≤ M :=
  (norm_sesquilinearOperator_le B).trans (B.opNorm_le_bound₂ hM hbound)

/-- Hermitian symmetry of the actual form gives self-adjointness. -/
theorem isSelfAdjoint_sesquilinearOperator (B : H →L⋆[ℂ] H →L[ℂ] ℂ)
    (hHermitian : ∀ x y, star (B y x) = B x y) :
    IsSelfAdjoint (sesquilinearOperator B) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (sesquilinearOperator B x) y = inner ℂ x (sesquilinearOperator B y)
  rw [← inner_conj_symm, inner_sesquilinearOperator, inner_sesquilinearOperator]
  exact hHermitian x y

/-- Positivity of the concrete quadratic form gives positivity of identity plus its operator. -/
theorem isPositive_id_add_sesquilinearOperator (B : H →L⋆[ℂ] H →L[ℂ] ℂ)
    (hHermitian : ∀ x y, star (B y x) = B x y)
    (hpositive : ∀ x, 0 ≤ ‖x‖ ^ 2 + (B x x).re) :
    (ContinuousLinearMap.id ℂ H + sesquilinearOperator B).IsPositive := by
  refine ⟨?_, ?_⟩
  · exact (ContinuousLinearMap.isPositive_id.isSelfAdjoint.add
      (isSelfAdjoint_sesquilinearOperator B hHermitian)).isSymmetric
  · intro x
    change 0 ≤ RCLike.re (inner ℂ ((ContinuousLinearMap.id ℂ H + sesquilinearOperator B) x) x)
    rw [inner_re_symm]
    simpa [inner_add_right, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow,
      RCLike.re_to_complex] using hpositive x

end GapFamily.Analytic
