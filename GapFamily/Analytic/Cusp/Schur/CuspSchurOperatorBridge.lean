import GapFamily.Analytic.Cusp.Schur.CuspSchurForm
import GapFamily.Analytic.Modular.ModularLaplacian

/-!
# Full weak equations and the actual modular operator domain

The true shifted Riesz solution identifies a full weak solution with a vector
in the actual Laplacian domain. Conversely the actual operator representation
gives the full test equation. These bridges require no spectral premise.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchur
open ModularGradient

theorem eq_weakSolution_of_formPairing (z : ℂ) (u : FormDomain) (f : ModularHilbert)
    (hu : ∀ t : FormDomain, formPairing z t u = inner ℂ (formEmbedding t) f) :
    u = weakSolution (f + (z + 1) • formEmbedding u) := by
  apply weakSolution_unique
  intro t
  have ht : inner ℂ (formGradient t) (formGradient u) +
      inner ℂ (formEmbedding t) (formEmbedding u) =
      inner ℂ (formEmbedding t) (f + (z + 1) • formEmbedding u) := by
    have h := hu t
    dsimp only [formPairing] at h
    rw [inner_add_right, inner_smul_right]
    linear_combination h
  have hc := congrArg (starRingEnd ℂ) ht
  simpa only [map_add, inner_conj_symm] using hc

theorem formEmbedding_mem_laplacian_domain_of_formPairing
    (z : ℂ) (u : FormDomain) (f : ModularHilbert)
    (hu : ∀ t : FormDomain, formPairing z t u = inner ℂ (formEmbedding t) f) :
    formEmbedding u ∈ laplacian.domain := by
  have hi : formEmbedding u = weakResolvent (f + (z + 1) • formEmbedding u) :=
    congrArg formEmbedding (eq_weakSolution_of_formPairing z u f hu)
  rw [hi]
  exact weakResolvent_mem_laplacian_domain _

theorem laplacian_sub_smul_of_formPairing (z : ℂ) (u : FormDomain) (f : ModularHilbert)
    (hu : ∀ t : FormDomain, formPairing z t u = inner ℂ (formEmbedding t) f) :
    laplacian ⟨formEmbedding u,
      formEmbedding_mem_laplacian_domain_of_formPairing z u f hu⟩ -
        z • formEmbedding u = f := by
  let g := f + (z + 1) • formEmbedding u
  have hi : formEmbedding u = weakResolvent g :=
    congrArg formEmbedding (eq_weakSolution_of_formPairing z u f hu)
  have hp : (⟨formEmbedding u,
      formEmbedding_mem_laplacian_domain_of_formPairing z u f hu⟩ : laplacian.domain) =
      ⟨weakResolvent g, weakResolvent_mem_laplacian_domain g⟩ := Subtype.ext hi
  have hr := laplacian_resolvent g
  rw [← hp, ← hi] at hr
  change laplacian ⟨formEmbedding u,
    formEmbedding_mem_laplacian_domain_of_formPairing z u f hu⟩ + formEmbedding u =
      f + (z + 1) • formEmbedding u at hr
  calc
    _ = (laplacian ⟨formEmbedding u,
          formEmbedding_mem_laplacian_domain_of_formPairing z u f hu⟩ + formEmbedding u) -
          (z + 1) • formEmbedding u := by module
    _ = f := by rw [hr]; abel

theorem formPairing_laplacian (z : ℂ) (x : laplacian.domain) (t : FormDomain) :
    formPairing z t (formLift ⟨x, laplacian_domain_le x.property⟩) =
      inner ℂ (formEmbedding t) (laplacian x - z • (x : ModularHilbert)) := by
  have h := congrArg (starRingEnd ℂ)
    (laplacian_representation x
      ⟨formEmbedding t, Dirichlet.gradientEmbedding_mem_domain closedGradient t⟩)
  simp only [inner_conj_symm] at h
  rw [← Dirichlet.gradientValue_apply closedGradient t] at h
  change inner ℂ (formEmbedding t) (laplacian x) =
    inner ℂ (formGradient t)
      (formGradient (formLift ⟨x, laplacian_domain_le x.property⟩)) at h
  unfold formPairing
  rw [inner_sub_right, inner_smul_right, h]
  rfl

end GapFamily.Analytic.CuspSchur
