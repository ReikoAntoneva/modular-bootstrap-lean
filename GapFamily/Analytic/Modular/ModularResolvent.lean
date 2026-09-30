import GapFamily.Analytic.Modular.ModularGradientWeak

/-!
# The actual modular energy form and its weak solution

The closed modular gradient gives a complete graph form space. The Riesz
solution is constructed on that space, satisfies the actual energy equation,
and fixes the constant channel. Domain density is not used here; identifying
the resulting map with the inverse of a densely defined Laplacian is separate.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory
open Dirichlet

/-- The actual complete modular form domain, with mass-plus-energy norm. -/
abbrev FormDomain := gradientGraph closedGradient

instance : CompleteSpace FormDomain :=
  gradientGraph_completeSpace closedGradient closedGradient_isClosed

abbrev formEmbedding : FormDomain →L[ℂ] ModularHilbert := gradientEmbedding closedGradient
abbrev formGradient : FormDomain →L[ℂ] GradientSpace := gradientValue closedGradient
abbrev formLift (u : closedGradient.domain) : FormDomain := gradientLift closedGradient u

theorem formEmbedding_injective : Function.Injective formEmbedding :=
  gradientEmbedding_injective closedGradient

theorem formDomain_norm_sq (u : FormDomain) :
    ‖u‖ ^ 2 = ‖formEmbedding u‖ ^ 2 + ‖formGradient u‖ ^ 2 :=
  gradientGraph_norm_sq closedGradient u

/-- The unique weak solution in the actual modular form space. -/
def weakSolution : ModularHilbert →L[ℂ] FormDomain :=
  formSolution (V := FormDomain) (H := ModularHilbert) formEmbedding

/-- The actual ambient Riesz solution map for energy plus mass. -/
def weakResolvent : ModularHilbert →L[ℂ] ModularHilbert :=
  formResolvent (V := FormDomain) (H := ModularHilbert) formEmbedding

theorem weakResolvent_apply (f : ModularHilbert) :
    weakResolvent f = formEmbedding (weakSolution f) := rfl

theorem weakResolvent_mem_domain (f : ModularHilbert) :
    weakResolvent f ∈ closedGradient.domain :=
  gradientEmbedding_mem_domain closedGradient (weakSolution f)

theorem weakSolution_equation (f : ModularHilbert) (v : FormDomain) :
    inner ℂ (formGradient (weakSolution f)) (formGradient v) +
      inner ℂ (weakResolvent f) (formEmbedding v) = inner ℂ f (formEmbedding v) := by
  have h := formSolution_weak (V := FormDomain) (H := ModularHilbert) formEmbedding f v
  rw [gradient_formEnergy] at h
  exact h

theorem weakSolution_unique (f : ModularHilbert) (u : FormDomain)
    (hu : ∀ v : FormDomain, inner ℂ (formGradient u) (formGradient v) +
      inner ℂ (formEmbedding u) (formEmbedding v) = inner ℂ f (formEmbedding v)) :
    u = weakSolution f := by
  apply formSolution_unique (V := FormDomain) (H := ModularHilbert) formEmbedding f u
  intro v
  rw [gradient_formEnergy]
  exact hu v

theorem weakResolvent_isPositive : weakResolvent.IsPositive := by
  unfold weakResolvent
  have h := formResolvent_isPositive (V := FormDomain) (H := ModularHilbert) formEmbedding
  exact h

theorem weakResolvent_isSelfAdjoint : IsSelfAdjoint weakResolvent := by
  unfold weakResolvent
  have h := formResolvent_isSelfAdjoint (V := FormDomain) (H := ModularHilbert) formEmbedding
  exact h

theorem weakSolution_norm_le (f : ModularHilbert) : ‖weakSolution f‖ ≤ ‖f‖ := by
  have hop : ‖weakSolution‖ ≤ 1 := by
    change ‖ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := FormDomain)
      (F := ModularHilbert) formEmbedding‖ ≤ 1
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact gradientEmbedding_norm_le_one closedGradient
  exact (weakSolution.le_opNorm f).trans (by nlinarith [norm_nonneg f])

theorem weakResolvent_norm_le_one : ‖weakResolvent‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  calc
    ‖weakResolvent f‖ ≤ ‖weakSolution f‖ :=
      gradientEmbedding_norm_le closedGradient (weakSolution f)
    _ ≤ 1 * ‖f‖ := by simpa only [one_mul] using weakSolution_norm_le f

/-- The actual gradient and mass obey the source norm bound. -/
theorem weakSolution_energy_bound (f : ModularHilbert) :
    ‖weakResolvent f‖ ^ 2 +
      ‖closedGradient ⟨weakResolvent f, weakResolvent_mem_domain f⟩‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have h := weakSolution_norm_le f
  have hn := formDomain_norm_sq (weakSolution f)
  rw [gradientValue_apply] at hn
  change ‖weakSolution f‖ ^ 2 = ‖weakResolvent f‖ ^ 2 +
    ‖closedGradient ⟨weakResolvent f, weakResolvent_mem_domain f⟩‖ ^ 2 at hn
  nlinarith [norm_nonneg (weakSolution f), norm_nonneg f]

theorem weakSolution_constant :
    weakSolution modularConstant =
      formLift ⟨modularConstant, modularConstant_mem_closedGradient_domain⟩ := by
  symm
  apply weakSolution_unique
  intro v
  change inner ℂ (closedGradient ⟨modularConstant,
    modularConstant_mem_closedGradient_domain⟩) (formGradient v) +
      inner ℂ modularConstant (formEmbedding v) = _
  rw [closedGradient_modularConstant, inner_zero_left, zero_add]

theorem weakResolvent_constant : weakResolvent modularConstant = modularConstant := by
  rw [weakResolvent_apply, weakSolution_constant]
  rfl

theorem weakResolvent_constantProjection (f : ModularHilbert) :
    weakResolvent (modularConstantProjection f) = modularConstantProjection f := by
  rw [modularConstantProjection_apply, map_smul, weakResolvent_constant]

theorem modularAverage_weakResolvent (f : ModularHilbert) :
    modularAverage (weakResolvent f) = modularAverage f := by
  have h := weakResolvent_isSelfAdjoint.isSymmetric modularConstant f
  change inner ℂ (weakResolvent modularConstant) f =
    inner ℂ modularConstant (weakResolvent f) at h
  rw [weakResolvent_constant] at h
  change (modularMeasure.real univ : ℂ)⁻¹ * inner ℂ modularConstant (weakResolvent f) =
    (modularMeasure.real univ : ℂ)⁻¹ * inner ℂ modularConstant f
  rw [← h]

theorem integral_weakResolvent (f : ModularHilbert) :
    ∫ z, weakResolvent f z ∂modularMeasure = ∫ z, f z ∂modularMeasure := by
  have h := weakResolvent_isSelfAdjoint.isSymmetric modularConstant f
  change inner ℂ (weakResolvent modularConstant) f =
    inner ℂ modularConstant (weakResolvent f) at h
  simpa only [weakResolvent_constant, modularConstant_inner] using h.symm

theorem constantProjection_weakResolvent (f : ModularHilbert) :
    modularConstantProjection (weakResolvent f) = modularConstantProjection f := by
  simp only [modularConstantProjection_apply, modularAverage_weakResolvent]

theorem weakResolvent_meanZeroProjection (f : ModularHilbert) :
    weakResolvent (modularMeanZeroProjection f) = modularMeanZeroProjection (weakResolvent f) := by
  simp only [modularMeanZeroProjection_eq, sub_apply, ContinuousLinearMap.id_apply,
    map_sub, weakResolvent_constantProjection, constantProjection_weakResolvent]

theorem weakResolvent_preserves_meanZero {f : ModularHilbert} (hf : f ∈ modularMeanZero) :
    weakResolvent f ∈ modularMeanZero := by
  rw [mem_modularMeanZero_iff, integral_weakResolvent]
  exact (mem_modularMeanZero_iff f).mp hf

theorem weakResolvent_norm : ‖weakResolvent‖ = 1 := by
  apply le_antisymm weakResolvent_norm_le_one
  have h := weakResolvent.le_opNorm modularConstant
  rw [weakResolvent_constant] at h
  have hpos : 0 < ‖modularConstant‖ := norm_pos_iff.mpr modularConstant_ne_zero
  nlinarith

end GapFamily.Analytic.ModularGradient
