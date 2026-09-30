import GapFamily.Analytic.Cusp.Scalar.CuspScalarFormLiftCore
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The actual scalar lift on the completed modular form domain

The core lift is extended using its proved bound in the genuine form norm.
Its literal ambient projection formula, scalar-subspace membership, vanishing
trace and energy bound pass through the proved density of the smooth graph
core. The trace is removed before taking the scalar channel.
-/

noncomputable section

namespace GapFamily.Analytic

open Set ModularGradient

private theorem scalarFormLiftCore_bound (F : smoothCore) :
    ‖cuspScalarFormLiftCore F‖ ≤ ‖cuspTraceFree‖ * ‖coreForm F‖ :=
  (cuspScalarFormLiftCore_norm_le F).trans (cuspTraceFreeCore_form_norm_le F)

/-- The actual continuous extension of the scalar lift after removing the trace. -/
def cuspScalarFormLift : FormDomain →L[ℂ] FormDomain :=
  cuspScalarFormLiftCore.extendOfNorm coreForm

/-- Exact agreement with the constructed scalar lift of every genuine core vector. -/
@[simp] theorem cuspScalarFormLift_coreForm (F : smoothCore) :
    cuspScalarFormLift (coreForm F) = cuspScalarFormLiftCore F :=
  LinearMap.extendOfNorm_eq coreForm_denseRange
    ⟨‖cuspTraceFree‖, scalarFormLiftCore_bound⟩ F

/-- The completed scalar lift is bounded by the actual trace-removal operator. -/
theorem cuspScalarFormLift_opNorm_le : ‖cuspScalarFormLift‖ ≤ ‖cuspTraceFree‖ :=
  LinearMap.opNorm_extendOfNorm_le coreForm_denseRange
    (norm_nonneg cuspTraceFree) scalarFormLiftCore_bound

/-- The value of the completed lift is the literal ambient scalar projection
of the actual trace-free form value. -/
theorem cuspScalarFormLift_embedding (u : FormDomain) :
    formEmbedding (cuspScalarFormLift u) =
      cuspScalarProjection (formEmbedding (cuspTraceFree u)) := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    formEmbedding (cuspScalarFormLift u) =
      cuspScalarProjection (formEmbedding (cuspTraceFree u))) u ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro F
    simpa only [cuspScalarFormLift_coreForm, cuspTraceFree_coreForm,
      formEmbedding_coreForm] using cuspScalarFormLiftCore_embedding F

/-- Every completed lift lies in the actual closed scalar form subspace. -/
theorem cuspScalarFormLift_mem (u : FormDomain) :
    cuspScalarFormLift u ∈ cuspScalarForm := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    cuspScalarFormLift u ∈ cuspScalarForm) u ?_ ?_
  · exact cuspScalarForm_isClosed.preimage cuspScalarFormLift.continuous
  · intro F
    rw [cuspScalarFormLift_coreForm]
    exact cuspScalarFormLiftCore_mem F

/-- The completed scalar lift retains its genuine zero boundary-average trace. -/
@[simp] theorem cuspScalarFormLift_trace_eq_zero (u : FormDomain) :
    cuspAverageTrace (cuspScalarFormLift u) = 0 := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    cuspAverageTrace (cuspScalarFormLift u) = 0) u ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · intro F
    rw [cuspScalarFormLift_coreForm]
    exact cuspScalarFormLiftCore_trace_eq_zero F

/-- The full form norm of the lift is bounded by the actual trace-free form norm. -/
theorem cuspScalarFormLift_norm_le (u : FormDomain) :
    ‖cuspScalarFormLift u‖ ≤ ‖cuspTraceFree u‖ := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    ‖cuspScalarFormLift u‖ ≤ ‖cuspTraceFree u‖) u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro F
    simpa only [cuspScalarFormLift_coreForm, cuspTraceFree_coreForm] using
      cuspScalarFormLiftCore_norm_le F

/-- The scalar lift does not increase the actual closed-gradient norm. -/
theorem cuspScalarFormLift_gradient_norm_le (u : FormDomain) :
    ‖formGradient (cuspScalarFormLift u)‖ ≤ ‖formGradient u‖ := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    ‖formGradient (cuspScalarFormLift u)‖ ≤ ‖formGradient u‖) u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro F
    simpa only [cuspScalarFormLift_coreForm, formGradient_coreForm] using
      cuspScalarFormLiftCore_gradient_norm_le F

/-- On the actual zero-trace kernel, the lift realizes the ambient scalar projection. -/
theorem cuspScalarFormLift_embedding_of_trace_eq_zero (u : FormDomain)
    (hu : cuspAverageTrace u = 0) :
    formEmbedding (cuspScalarFormLift u) = cuspScalarProjection (formEmbedding u) := by
  rw [cuspScalarFormLift_embedding, cuspTraceFree_eq_self hu]

/-- The scalar lift is contractive on the actual zero-trace form kernel. -/
theorem cuspScalarFormLift_norm_le_of_trace_eq_zero (u : FormDomain)
    (hu : cuspAverageTrace u = 0) : ‖cuspScalarFormLift u‖ ≤ ‖u‖ := by
  simpa only [cuspTraceFree_eq_self hu] using cuspScalarFormLift_norm_le u

/-- Reapplying the completed scalar lift does not change its value. -/
@[simp] theorem cuspScalarFormLift_idempotent (u : FormDomain) :
    cuspScalarFormLift (cuspScalarFormLift u) = cuspScalarFormLift u := by
  apply formEmbedding_injective
  rw [cuspScalarFormLift_embedding_of_trace_eq_zero _
    (cuspScalarFormLift_trace_eq_zero u), cuspScalarFormLift_embedding]
  exact cuspScalarProjection_idempotent (formEmbedding (cuspTraceFree u))

end GapFamily.Analytic
