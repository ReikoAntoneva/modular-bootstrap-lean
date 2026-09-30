import GapFamily.Analytic.Cusp.Scalar.CuspScalarQuarter

/-!
# The actual scalar cusp Riesz response

The complete scalar form space gives a genuine shifted weak source solution.
The quarter-energy bound controls its ambient response by four fifths. Positivity,
selfadjointness and the actual test-first weak equation require no ambient density premise.
-/

noncomputable section

namespace GapFamily.Analytic

open ModularGradient

private theorem formResolvent_norm_sq {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (i : V →L[ℂ] H) : ‖Dirichlet.formResolvent i‖ = ‖i‖ ^ 2 := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self i.adjoint
  simpa only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint.norm_map,
    pow_two, Dirichlet.formResolvent] using h

/-- The actual closed gradient restricted to the scalar form space. -/
def cuspScalarGradient : cuspScalarForm →L[ℂ] GradientSpace :=
  formGradient.comp cuspScalarForm.subtypeL

theorem cuspScalarForm_energy (u v : cuspScalarForm) :
    Dirichlet.formEnergy scalarCuspEmbedding u v =
      inner ℂ (cuspScalarGradient u) (cuspScalarGradient v) := by
  change Dirichlet.formEnergy formEmbedding (u : FormDomain) (v : FormDomain) = _
  exact Dirichlet.gradient_formEnergy closedGradient u v

/-- The actual scalar shifted weak source response, without an ambient density premise. -/
def cuspScalarWeakSolution : ModularHilbert →L[ℂ] cuspScalarForm :=
  Dirichlet.formSolution (V := cuspScalarForm) (H := ModularHilbert) scalarCuspEmbedding

def cuspScalarWeakResolvent : ModularHilbert →L[ℂ] ModularHilbert :=
  Dirichlet.formResolvent (V := cuspScalarForm) (H := ModularHilbert) scalarCuspEmbedding

@[simp] theorem cuspScalarWeakResolvent_apply (f : ModularHilbert) :
    cuspScalarWeakResolvent f = scalarCuspEmbedding (cuspScalarWeakSolution f) := rfl

theorem scalarCuspEmbedding_opNorm_le : ‖scalarCuspEmbedding‖ ≤ Real.sqrt (4 / 5 : ℝ) := by
  apply @ContinuousLinearMap.opNorm_le_bound ℂ ℂ cuspScalarForm ModularHilbert
    (inferInstance : SeminormedAddCommGroup cuspScalarForm)
    (inferInstance : SeminormedAddCommGroup ModularHilbert) inferInstance inferInstance
    (inferInstance : NormedSpace ℂ cuspScalarForm)
    (inferInstance : NormedSpace ℂ ModularHilbert) (RingHom.id ℂ)
    scalarCuspEmbedding (Real.sqrt (4 / 5 : ℝ)) (Real.sqrt_nonneg _)
  intro w
  have h := scalarCuspEmbedding_norm_sq_le w
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 5)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, hs]
  exact h

theorem cuspScalarWeakResolvent_norm_le : ‖cuspScalarWeakResolvent‖ ≤ (4 / 5 : ℝ) := by
  have heq : ‖cuspScalarWeakResolvent‖ = ‖scalarCuspEmbedding‖ ^ 2 := by
    unfold cuspScalarWeakResolvent
    have h := formResolvent_norm_sq (V := cuspScalarForm) (H := ModularHilbert) scalarCuspEmbedding
    exact h
  rw [heq]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 5)
  have hn := scalarCuspEmbedding_opNorm_le
  nlinarith [norm_nonneg scalarCuspEmbedding]

theorem cuspScalarWeakResolvent_isPositive : cuspScalarWeakResolvent.IsPositive := by
  unfold cuspScalarWeakResolvent Dirichlet.formResolvent
  have h := ContinuousLinearMap.isPositive_self_comp_adjoint
    (𝕜 := ℂ) (E := cuspScalarForm) (F := ModularHilbert) scalarCuspEmbedding
  exact h

theorem cuspScalarWeakResolvent_isSelfAdjoint : IsSelfAdjoint cuspScalarWeakResolvent :=
  cuspScalarWeakResolvent_isPositive.isSelfAdjoint

/-- Every actual scalar test satisfies the literal shifted weak equation. -/
theorem cuspScalarWeakSolution_equation (f : ModularHilbert) (v : cuspScalarForm) :
    inner ℂ (cuspScalarGradient v) (cuspScalarGradient (cuspScalarWeakSolution f)) +
      inner ℂ (scalarCuspEmbedding v) (cuspScalarWeakResolvent f) =
        inner ℂ (scalarCuspEmbedding v) f := by
  have h := congrArg (starRingEnd ℂ)
    (Dirichlet.formSolution_weak (V := cuspScalarForm) (H := ModularHilbert)
      scalarCuspEmbedding f v)
  rw [cuspScalarForm_energy] at h
  simpa only [map_add, inner_conj_symm, cuspScalarWeakSolution, cuspScalarWeakResolvent] using h

theorem cuspScalarWeakSolution_unique (f : ModularHilbert) (u : cuspScalarForm)
    (hu : ∀ v : cuspScalarForm,
      inner ℂ (cuspScalarGradient v) (cuspScalarGradient u) +
        inner ℂ (scalarCuspEmbedding v) (scalarCuspEmbedding u) =
          inner ℂ (scalarCuspEmbedding v) f) : u = cuspScalarWeakSolution f := by
  apply Dirichlet.formSolution_unique (V := cuspScalarForm) (H := ModularHilbert)
    scalarCuspEmbedding f u
  intro v
  rw [cuspScalarForm_energy]
  have h := congrArg (starRingEnd ℂ) (hu v)
  simpa only [map_add, inner_conj_symm] using h

end GapFamily.Analytic
