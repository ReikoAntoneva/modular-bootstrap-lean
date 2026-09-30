import Mathlib.Analysis.InnerProductSpace.Positive
import GapFamily.Analytic.Elliptic.DirichletInverse

/-!
# A closed nonnegative form from its complete form-domain embedding

For an injective dense continuous contraction `i : V →L[ℂ] H`, the complete
Hilbert space `V` is a closed nonnegative form domain in `H`. The form is the
difference of the form-space and ambient inner products. Its shifted form
norm is exactly the given complete norm of `V`.
The weak resolvent is constructed as `i ∘ i.adjoint`; no Laplacian or resolvent
is assumed. Injectivity, density and contractivity of an actual modular form
embedding remain separate application obligations.
-/

namespace GapFamily.Analytic.Dirichlet

open Complex ContinuousLinearMap
open scoped ComplexConjugate

noncomputable section

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The sesquilinear energy form encoded by the complete form-domain norm. -/
def formEnergy (i : V →L[ℂ] H) (u v : V) : ℂ :=
  inner ℂ u v - inner ℂ (i u) (i v)

theorem formEnergy_conj_symm (i : V →L[ℂ] H) (u v : V) :
    conj (formEnergy i u v) = formEnergy i v u := by
  simp [formEnergy, inner_conj_symm]

theorem formEnergy_add_right (i : V →L[ℂ] H) (u v w : V) :
    formEnergy i u (v + w) = formEnergy i u v + formEnergy i u w := by
  simp only [formEnergy, map_add, inner_add_right]
  ring

theorem formEnergy_smul_right (i : V →L[ℂ] H) (u v : V) (a : ℂ) :
    formEnergy i u (a • v) = a * formEnergy i u v := by
  simp only [formEnergy, map_smul, inner_smul_right]
  ring

theorem formEnergy_self (i : V →L[ℂ] H) (u : V) :
    (formEnergy i u u).re = ‖u‖ ^ 2 - ‖i u‖ ^ 2 := by
  simp [formEnergy, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- The shifted form norm is precisely the complete Hilbert norm on `V`. -/
theorem formEnergy_add_mass (i : V →L[ℂ] H) (u : V) :
    (formEnergy i u u).re + ‖i u‖ ^ 2 = ‖u‖ ^ 2 := by
  rw [formEnergy_self]
  ring

theorem embedding_norm_le (i : V →L[ℂ] H) (hi : ‖i‖ ≤ 1) (u : V) : ‖i u‖ ≤ ‖u‖ :=
  (i.le_opNorm u).trans (by nlinarith [norm_nonneg u])

theorem formEnergy_nonneg (i : V →L[ℂ] H) (hi : ‖i‖ ≤ 1) (u : V) :
    0 ≤ (formEnergy i u u).re := by
  rw [formEnergy_self]
  have h := embedding_norm_le i hi u
  nlinarith [norm_nonneg u, norm_nonneg (i u)]

variable [CompleteSpace V] [CompleteSpace H]

/-- The weak solution in form coordinates is the Riesz adjoint of the embedding. -/
def formSolution (i : V →L[ℂ] H) : H →L[ℂ] V := i.adjoint

/-- The ambient weak resolvent `(A+1)⁻¹`, explicitly constructed from the form. -/
def formResolvent (i : V →L[ℂ] H) : H →L[ℂ] H := i.comp i.adjoint

@[simp] theorem formResolvent_apply (i : V →L[ℂ] H) (f : H) :
    formResolvent i f = i (formSolution i f) := rfl

/-- The weak equation contains the actual energy form and mass inner product. -/
theorem formSolution_weak (i : V →L[ℂ] H) (f : H) (v : V) :
    formEnergy i (formSolution i f) v + inner ℂ (formResolvent i f) (i v) =
      inner ℂ f (i v) := by
  simp only [formEnergy, formResolvent_apply, sub_add_cancel, formSolution]
  exact i.adjoint_inner_left v f

theorem formSolution_unique (i : V →L[ℂ] H) (f : H) (u : V)
    (hu : ∀ v : V, formEnergy i u v + inner ℂ (i u) (i v) = inner ℂ f (i v)) :
    u = formSolution i f := by
  apply ext_inner_right ℂ
  intro v
  simpa only [formEnergy, sub_add_cancel, formSolution, i.adjoint_inner_left] using hu v

theorem existsUnique_formSolution (i : V →L[ℂ] H) (f : H) :
    ∃! u : V, ∀ v : V,
      formEnergy i u v + inner ℂ (i u) (i v) = inner ℂ f (i v) := by
  refine ⟨formSolution i f, formSolution_weak i f, ?_⟩
  exact fun u hu => formSolution_unique i f u hu

theorem formResolvent_isPositive (i : V →L[ℂ] H) : (formResolvent i).IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint i

theorem formResolvent_isSelfAdjoint (i : V →L[ℂ] H) : IsSelfAdjoint (formResolvent i) :=
  (formResolvent_isPositive i).isSelfAdjoint

theorem formSolution_injective (i : V →L[ℂ] H) (hi : DenseRange i) :
    Function.Injective (formSolution i) := by
  intro f g hfg
  apply hi.eq_of_inner_right ℂ
  intro u
  rw [← i.adjoint_inner_right, ← i.adjoint_inner_right]
  exact congrArg (inner ℂ u) hfg

theorem formResolvent_injective (i : V →L[ℂ] H) (hi : DenseRange i) :
    Function.Injective (formResolvent i) :=
  i.self_comp_adjoint_injective_iff.mpr (formSolution_injective i hi)

theorem formResolvent_denseRange (i : V →L[ℂ] H) (hi : DenseRange i) :
    DenseRange (formResolvent i) := by
  change Dense ((formResolvent i).range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_orthogonal_eq_closure,
    ContinuousLinearMap.orthogonal_range, (formResolvent_isSelfAdjoint i).adjoint_eq,
    LinearMap.ker_eq_bot.mpr (formResolvent_injective i hi), Submodule.bot_orthogonal_eq_top]

theorem formResolvent_norm_le_one (i : V →L[ℂ] H) (hi : ‖i‖ ≤ 1) :
    ‖formResolvent i‖ ≤ 1 := by
  calc
    ‖formResolvent i‖ ≤ ‖i‖ * ‖i.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖i‖ * ‖i‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 := by nlinarith [norm_nonneg i]

/-- The operator is constructed on the actual range of its weak resolvent.
Identification with the form on all of `V` additionally uses injectivity of `i`. -/
def formOperator (i : V →L[ℂ] H) (hi : DenseRange i) : H →ₗ.[ℂ] H :=
  inverseShift (formResolvent i) (formResolvent_injective i hi)

@[simp] theorem formOperator_domain (i : V →L[ℂ] H) (hi : DenseRange i) :
    (formOperator i hi).domain = (formResolvent i).range := rfl

theorem formOperator_isSelfAdjoint (i : V →L[ℂ] H) (hi : DenseRange i) :
    IsSelfAdjoint (formOperator i hi) :=
  inverseShift_isSelfAdjoint (formResolvent i) (formResolvent_injective i hi)
    (formResolvent_denseRange i hi) (formResolvent_isSelfAdjoint i).isSymmetric

theorem formOperator_isClosed (i : V →L[ℂ] H) (hi : DenseRange i) :
    (formOperator i hi).IsClosed := (formOperator_isSelfAdjoint i hi).isClosed

theorem formOperator_dense_domain (i : V →L[ℂ] H) (hi : DenseRange i) :
    Dense ((formOperator i hi).domain : Set H) := (formOperator_isSelfAdjoint i hi).dense_domain

/-- The constructed operator and weak resolvent satisfy the actual inverse identity. -/
theorem formOperator_apply_resolvent (i : V →L[ℂ] H) (hi : DenseRange i) (f : H) :
    formOperator i hi ⟨formResolvent i f, LinearMap.mem_range_self _ f⟩ +
      formResolvent i f = f :=
  inverseShift_apply_range_add (formResolvent i) (formResolvent_injective i hi) f

/-- Every operator-domain vector has a canonical lift to the complete form space. -/
def formOperatorLift (i : V →L[ℂ] H) (hi : DenseRange i)
    (u : (formOperator i hi).domain) : V :=
  formSolution i (formOperator i hi u + u)

@[simp] theorem formOperatorLift_embedding (i : V →L[ℂ] H) (hi : DenseRange i)
    (u : (formOperator i hi).domain) : i (formOperatorLift i hi u) = u :=
  inverseShift_image_apply_add (formResolvent i) (formResolvent_injective i hi) u

/-- The operator represents the energy form on its canonical lifted domain.
The full ambient form interpretation is supplied by `formOperator_domain_iff`
under an injective embedding; no descent of a noninjective form is claimed. -/
theorem formOperator_representation (i : V →L[ℂ] H) (hi : DenseRange i)
    (u : (formOperator i hi).domain) (v : V) :
    inner ℂ (formOperator i hi u) (i v) = formEnergy i (formOperatorLift i hi u) v := by
  have h := formSolution_weak i (formOperator i hi u + u) v
  change formEnergy i (formOperatorLift i hi u) v +
    inner ℂ (i (formOperatorLift i hi u)) (i v) = _ at h
  rw [formOperatorLift_embedding, inner_add_left] at h
  exact (add_right_cancel h).symm

theorem formOperator_nonnegative (i : V →L[ℂ] H) (hi : DenseRange i)
    (hcontract : ‖i‖ ≤ 1) (u : (formOperator i hi).domain) :
    0 ≤ (inner ℂ (formOperator i hi u) (u : H)).re := by
  have h := formOperator_representation i hi u (formOperatorLift i hi u)
  rw [formOperatorLift_embedding] at h
  rw [h]
  exact formEnergy_nonneg i hcontract _

/-- Exact form-domain characterization of the constructed operator domain.
Injectivity says the complete form-space vectors are actual ambient vectors. -/
theorem formOperator_domain_iff (i : V →L[ℂ] H) (hi : DenseRange i)
    (hinj : Function.Injective i) (u : V) :
    i u ∈ (formOperator i hi).domain ↔
      ∃ f : H, ∀ v : V, formEnergy i u v = inner ℂ f (i v) := by
  constructor
  · intro hu
    let U : (formOperator i hi).domain := ⟨i u, hu⟩
    have hlift : formOperatorLift i hi U = u := hinj (formOperatorLift_embedding i hi U)
    refine ⟨formOperator i hi U, ?_⟩
    intro v
    rw [← hlift]
    exact (formOperator_representation i hi U v).symm
  · rintro ⟨f, hf⟩
    have hsol : u = formSolution i (f + i u) := by
      apply formSolution_unique
      intro v
      rw [hf, inner_add_left]
    change i u ∈ (formResolvent i).range
    refine ⟨f + i u, ?_⟩
    change i (formSolution i (f + i u)) = i u
    rw [← hsol]

/-- Weak energy representation identifies the operator value uniquely. -/
theorem formOperator_value_of_weak (i : V →L[ℂ] H) (hi : DenseRange i)
    (hinj : Function.Injective i) (u : V) (f : H)
    (hf : ∀ v : V, formEnergy i u v = inner ℂ f (i v)) :
    formOperator i hi ⟨i u, (formOperator_domain_iff i hi hinj u).mpr ⟨f, hf⟩⟩ = f := by
  let U : (formOperator i hi).domain :=
    ⟨i u, (formOperator_domain_iff i hi hinj u).mpr ⟨f, hf⟩⟩
  have hlift : formOperatorLift i hi U = u := hinj (formOperatorLift_embedding i hi U)
  apply hi.eq_of_inner_left ℂ
  intro v
  change inner ℂ (formOperator i hi U) (i v) = inner ℂ f (i v)
  rw [formOperator_representation, hlift, hf]

/-- Completion of the square for the source quadratic of a Hilbert form embedding. -/
theorem form_variational_identity (i : V →L[ℂ] H) (f : H) (u : V) :
    ‖u‖ ^ 2 - 2 * (inner ℂ f (i u)).re =
      ‖u - i.adjoint f‖ ^ 2 - ‖i.adjoint f‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_re_symm u (i.adjoint f), i.adjoint_inner_left,
    add_sub_cancel_right]
  rfl

/-- The exact lower bound of the source quadratic. -/
theorem form_variational_lower_bound (i : V →L[ℂ] H) (f : H) (u : V) :
    -‖i.adjoint f‖ ^ 2 ≤ ‖u‖ ^ 2 - 2 * (inner ℂ f (i u)).re := by
  rw [form_variational_identity]
  simpa only [zero_sub] using sub_le_sub_right (sq_nonneg ‖u - i.adjoint f‖) (‖i.adjoint f‖ ^ 2)

/-- Equality at the lower bound characterizes the weak solution uniquely. -/
theorem form_variational_eq_lower_bound_iff (i : V →L[ℂ] H) (f : H) (u : V) :
    ‖u‖ ^ 2 - 2 * (inner ℂ f (i u)).re = -‖i.adjoint f‖ ^ 2 ↔
      u = i.adjoint f := by
  rw [form_variational_identity, sub_eq_neg_self, pow_eq_zero_iff (by norm_num : 2 ≠ 0),
    norm_eq_zero, sub_eq_zero]

/-- The adjoint source is the unique global minimizer of the actual quadratic. -/
theorem form_variational_minimizer_iff (i : V →L[ℂ] H) (f : H) (u : V) :
    (∀ v : V, ‖u‖ ^ 2 - 2 * (inner ℂ f (i u)).re ≤
      ‖v‖ ^ 2 - 2 * (inner ℂ f (i v)).re) ↔ u = i.adjoint f := by
  constructor
  · intro h
    apply (form_variational_eq_lower_bound_iff i f u).mp
    apply le_antisymm
    · simpa only [(form_variational_eq_lower_bound_iff i f (i.adjoint f)).mpr rfl]
        using h (i.adjoint f)
    · exact form_variational_lower_bound i f u
  · rintro rfl v
    rw [(form_variational_eq_lower_bound_iff i f (i.adjoint f)).mpr rfl]
    exact form_variational_lower_bound i f v

/-- The exact energy-plus-mass objective in the source's weak minimization. -/
def formObjective (i : V →L[ℂ] H) (f : H) (u : V) : ℝ :=
  (formEnergy i u u).re + ‖i u‖ ^ 2 - 2 * (inner ℂ f (i u)).re

theorem formObjective_eq (i : V →L[ℂ] H) (f : H) (u : V) :
    formObjective i f u = ‖u - formSolution i f‖ ^ 2 - ‖formSolution i f‖ ^ 2 := by
  rw [formObjective, formEnergy_add_mass]
  exact form_variational_identity i f u

/-- The weak solution is the unique global minimizer of the actual source objective. -/
theorem formObjective_minimizer_iff (i : V →L[ℂ] H) (f : H) (u : V) :
    (∀ v : V, formObjective i f u ≤ formObjective i f v) ↔ u = formSolution i f := by
  simp only [formObjective, formEnergy_add_mass, formSolution]
  exact form_variational_minimizer_iff i f u

end

end GapFamily.Analytic.Dirichlet
