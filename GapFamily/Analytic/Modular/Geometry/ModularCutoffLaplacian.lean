import GapFamily.Analytic.Modular.Geometry.ModularCutoffCommutator
import GapFamily.Analytic.Modular.Geometry.ModularCutoffFrameProduct

noncomputable section
namespace GapFamily.Analytic.ModularGradient.InteriorCutoff
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

def operatorForm (u : laplacian.domain) : FormDomain :=
  formLift ⟨u, laplacian_domain_le u.property⟩

theorem operatorForm_value (u : laplacian.domain) : formEmbedding (operatorForm u) = u := rfl

theorem operatorForm_representation (u : laplacian.domain) (v : FormDomain) :
    inner ℂ (laplacian u) (formEmbedding v) =
      inner ℂ (formGradient (operatorForm u)) (formGradient v) := by
  change inner ℂ (laplacian u) (formEmbedding v) =
    inner ℂ (closedGradient ⟨u, laplacian_domain_le u.property⟩)
      (Dirichlet.gradientValue closedGradient v)
  rw [Dirichlet.gradientValue_apply]
  exact laplacian_representation u
    ⟨formEmbedding v, Dirichlet.gradientEmbedding_mem_domain closedGradient v⟩

def commutatorValue (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (u : laplacian.domain) : ModularHilbert :=
  valueMultiplier χ hχ hc (laplacian u) +
    secondMultiplier χ hχ hc 1 u + secondMultiplier χ hχ hc Complex.I u -
    (2 : ℂ) • (derivativeMultiplier χ hχ hc 1 (formGradient (operatorForm u)).fst +
      derivativeMultiplier χ hχ hc Complex.I (formGradient (operatorForm u)).snd)


theorem commutatorValue_core_pairing (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (u : laplacian.domain) (F : smoothCore) :
    inner ℂ (commutatorValue χ hχ hc u) (value F) =
      inner ℂ (formGradient (formMultiplier χ hχ hc hs (operatorForm u))) (coreGradient F) := by
  have hrep := operatorForm_representation u (formMultiplier χ hχ hc hs (coreForm F))
  rw [formMultiplier_value, formEmbedding_coreForm,
    formMultiplier_gradient, formGradient_coreForm, formEmbedding_coreForm] at hrep
  change inner ℂ (laplacian u) (valueMultiplier χ hχ hc (value F)) =
    inner ℂ (formGradient (operatorForm u)).fst
      (valueMultiplier χ hχ hc (xComponent F) + derivativeMultiplier χ hχ hc 1 (value F)) +
    inner ℂ (formGradient (operatorForm u)).snd
      (valueMultiplier χ hχ hc (yComponent F) + derivativeMultiplier χ hχ hc Complex.I (value F)) at hrep
  rw [inner_add_right, inner_add_right,
    ← valueMultiplier_inner, ← valueMultiplier_inner, ← valueMultiplier_inner,
    ← derivativeMultiplier_inner, ← derivativeMultiplier_inner] at hrep
  have hx := derivativeMultiplier_ibp_x χ hχ hc hs (operatorForm u) F
  have hy := derivativeMultiplier_ibp_y χ hχ hc hs (operatorForm u) F
  rw [operatorForm_value] at hx hy
  rw [formMultiplier_gradient]
  change inner ℂ (commutatorValue χ hχ hc u) (value F) =
    inner ℂ (valueMultiplier χ hχ hc (formGradient (operatorForm u)).fst +
      derivativeMultiplier χ hχ hc 1 (formEmbedding (operatorForm u))) (xComponent F) +
    inner ℂ (valueMultiplier χ hχ hc (formGradient (operatorForm u)).snd +
      derivativeMultiplier χ hχ hc Complex.I (formEmbedding (operatorForm u))) (yComponent F)
  simp only [commutatorValue, inner_add_left, inner_sub_left, inner_smul_left,
    map_ofNat, operatorForm_value]
  linear_combination hrep - hx - hy

theorem commutatorValue_form_pairing (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (u : laplacian.domain) (v : FormDomain) :
    inner ℂ (commutatorValue χ hχ hc u) (formEmbedding v) =
      inner ℂ (formGradient (formMultiplier χ hχ hc hs (operatorForm u))) (formGradient v) := by
  refine coreForm_denseRange.induction_on (p := fun v : FormDomain =>
    inner ℂ (commutatorValue χ hχ hc u) (formEmbedding v) =
      inner ℂ (formGradient (formMultiplier χ hχ hc hs (operatorForm u))) (formGradient v)) v ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro F
    simpa only [formEmbedding_coreForm, formGradient_coreForm] using
      commutatorValue_core_pairing χ hχ hc hs u F

theorem formMultiplier_mem_laplacian_domain (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (u : laplacian.domain) :
    formEmbedding (formMultiplier χ hχ hc hs (operatorForm u)) ∈ laplacian.domain := by
  let w := formMultiplier χ hχ hc hs (operatorForm u)
  have hw : formEmbedding w ∈ closedGradient.domain :=
    Dirichlet.gradientEmbedding_mem_domain closedGradient w
  apply (laplacian_domain_iff ⟨formEmbedding w, hw⟩).mpr
  apply closedGradient.mem_adjoint_domain_of_exists
  refine ⟨commutatorValue χ hχ hc u, fun v => ?_⟩
  have h := commutatorValue_form_pairing χ hχ hc hs u (formLift v)
  change inner ℂ (commutatorValue χ hχ hc u) v =
    inner ℂ (formGradient w) (closedGradient v) at h
  rw [Dirichlet.gradientValue_apply] at h
  exact h

theorem laplacian_formMultiplier (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (u : laplacian.domain) :
    laplacian ⟨formEmbedding (formMultiplier χ hχ hc hs (operatorForm u)),
      formMultiplier_mem_laplacian_domain χ hχ hc hs u⟩ = commutatorValue χ hχ hc u := by
  apply formEmbedding_denseRange.eq_of_inner_left ℂ
  intro v
  have h := laplacian_representation
    ⟨formEmbedding (formMultiplier χ hχ hc hs (operatorForm u)),
      formMultiplier_mem_laplacian_domain χ hχ hc hs u⟩
    ⟨formEmbedding v, Dirichlet.gradientEmbedding_mem_domain closedGradient v⟩
  have hv := commutatorValue_form_pairing χ hχ hc hs u v
  rw [Dirichlet.gradientValue_apply, Dirichlet.gradientValue_apply] at hv
  exact h.trans hv.symm

end GapFamily.Analytic.ModularGradient.InteriorCutoff
