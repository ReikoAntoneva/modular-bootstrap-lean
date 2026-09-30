import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroCompact

/-!
# The actual constrained weak solution and compact response

The Riesz adjoint of the proved compact form embedding constructs the weak
solution with zero horizontal cusp average. Its ambient response is compact,
positive and selfadjoint. No density in an independently specified ambient
constrained Hilbert space, or unbounded-operator domain, is assumed here.
-/

noncomputable section

namespace GapFamily.Analytic

open ModularGradient

/-- The actual closed gradient restricted to the constrained form space. -/
def cuspMeanZeroGradient : cuspMeanZeroForm →L[ℂ] GradientSpace :=
  formGradient.comp cuspMeanZeroForm.subtypeL

theorem cuspMeanZeroForm_norm_sq (u : cuspMeanZeroForm) :
    ‖u‖ ^ 2 = ‖meanZeroCuspEmbedding u‖ ^ 2 + ‖cuspMeanZeroGradient u‖ ^ 2 :=
  formDomain_norm_sq u

theorem meanZeroCuspEmbedding_norm_le (u : cuspMeanZeroForm) :
    ‖meanZeroCuspEmbedding u‖ ≤ ‖u‖ :=
  Dirichlet.gradientEmbedding_norm_le closedGradient u

theorem meanZeroCuspEmbedding_opNorm_le_one : ‖meanZeroCuspEmbedding‖ ≤ 1 := by
  exact @ContinuousLinearMap.opNorm_le_bound ℂ ℂ cuspMeanZeroForm ModularHilbert
    (inferInstance : SeminormedAddCommGroup cuspMeanZeroForm)
    (inferInstance : SeminormedAddCommGroup ModularHilbert) inferInstance inferInstance
    (inferInstance : NormedSpace ℂ cuspMeanZeroForm)
    (inferInstance : NormedSpace ℂ ModularHilbert) (RingHom.id ℂ)
    meanZeroCuspEmbedding 1 zero_le_one
    (fun u => by simpa only [one_mul] using meanZeroCuspEmbedding_norm_le u)

/-- The inherited form energy is exactly the genuine closed-gradient energy. -/
theorem cuspMeanZeroForm_energy (u v : cuspMeanZeroForm) :
    Dirichlet.formEnergy meanZeroCuspEmbedding u v =
      inner ℂ (cuspMeanZeroGradient u) (cuspMeanZeroGradient v) := by
  change Dirichlet.formEnergy formEmbedding (u : FormDomain) (v : FormDomain) = _
  exact Dirichlet.gradient_formEnergy closedGradient u v

/-- The actual Riesz source solution in the complete constrained form space. -/
def cuspMeanZeroWeakSolution : ModularHilbert →L[ℂ] cuspMeanZeroForm :=
  Dirichlet.formSolution (V := cuspMeanZeroForm) (H := ModularHilbert) meanZeroCuspEmbedding

/-- The actual ambient response `i i†`; the ambient null channel is retained. -/
def cuspMeanZeroWeakResolvent : ModularHilbert →L[ℂ] ModularHilbert :=
  Dirichlet.formResolvent (V := cuspMeanZeroForm) (H := ModularHilbert) meanZeroCuspEmbedding

theorem cuspMeanZeroWeakResolvent_apply (f : ModularHilbert) :
    cuspMeanZeroWeakResolvent f = meanZeroCuspEmbedding (cuspMeanZeroWeakSolution f) := rfl

theorem cuspMeanZeroWeakResolvent_isCompact : IsCompactOperator cuspMeanZeroWeakResolvent :=
  isCompactOperator_meanZeroCuspEmbedding.comp_clm cuspMeanZeroWeakSolution

theorem cuspMeanZeroWeakResolvent_isPositive : cuspMeanZeroWeakResolvent.IsPositive := by
  unfold cuspMeanZeroWeakResolvent Dirichlet.formResolvent
  have h := ContinuousLinearMap.isPositive_self_comp_adjoint
    (𝕜 := ℂ) (E := cuspMeanZeroForm) (F := ModularHilbert) meanZeroCuspEmbedding
  exact h

theorem cuspMeanZeroWeakResolvent_isSelfAdjoint : IsSelfAdjoint cuspMeanZeroWeakResolvent :=
  cuspMeanZeroWeakResolvent_isPositive.isSelfAdjoint

/-- The actual gradient-plus-mass equation holds for every constrained test vector. -/
theorem cuspMeanZeroWeakSolution_equation (f : ModularHilbert) (v : cuspMeanZeroForm) :
    inner ℂ (cuspMeanZeroGradient (cuspMeanZeroWeakSolution f)) (cuspMeanZeroGradient v) +
      inner ℂ (cuspMeanZeroWeakResolvent f) (meanZeroCuspEmbedding v) =
        inner ℂ f (meanZeroCuspEmbedding v) := by
  have h := Dirichlet.formSolution_weak (V := cuspMeanZeroForm) (H := ModularHilbert)
    meanZeroCuspEmbedding f v
  rw [cuspMeanZeroForm_energy] at h
  exact h

theorem cuspMeanZeroWeakSolution_unique (f : ModularHilbert) (u : cuspMeanZeroForm)
    (hu : ∀ v : cuspMeanZeroForm,
      inner ℂ (cuspMeanZeroGradient u) (cuspMeanZeroGradient v) +
        inner ℂ (meanZeroCuspEmbedding u) (meanZeroCuspEmbedding v) =
          inner ℂ f (meanZeroCuspEmbedding v)) :
    u = cuspMeanZeroWeakSolution f := by
  apply Dirichlet.formSolution_unique (V := cuspMeanZeroForm) (H := ModularHilbert)
    meanZeroCuspEmbedding f u
  intro v
  rw [cuspMeanZeroForm_energy]
  exact hu v

end GapFamily.Analytic
