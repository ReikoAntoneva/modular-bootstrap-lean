import GapFamily.Analytic.Modular.ModularResolvent
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationDensity

/-!
# The actual nonnegative selfadjoint modular Laplacian

Smooth automorphic periodization proves density of the concrete gradient
domain. Its proved graph closure therefore defines a genuine selfadjoint
operator by the energy form. The domain is exactly that of `D†D`, and the
constructed weak solution is its shifted inverse. No spectral continuation,
kernel uniqueness, or compactness theorem is asserted here.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory Dirichlet

/-- The form realization of the actual closed modular gradient. -/
abbrev laplacian : ModularHilbert →ₗ.[ℂ] ModularHilbert :=
  closedGradientOperator closedGradient closedGradient_isClosed closedGradient_dense_domain

theorem laplacian_isSelfAdjoint : IsSelfAdjoint laplacian :=
  closedGradientOperator_isSelfAdjoint _ _ _

theorem laplacian_isClosed : laplacian.IsClosed := laplacian_isSelfAdjoint.isClosed

theorem laplacian_dense_domain : Dense (laplacian.domain : Set ModularHilbert) :=
  laplacian_isSelfAdjoint.dense_domain

theorem laplacian_nonnegative (u : laplacian.domain) :
    0 ≤ (inner ℂ (laplacian u) (u : ModularHilbert)).re :=
  closedGradientOperator_nonnegative _ _ _ u

theorem laplacian_domain_le : laplacian.domain ≤ closedGradient.domain :=
  closedGradientOperator_domain_le _ _ _

theorem laplacian_representation (u : laplacian.domain) (v : closedGradient.domain) :
    inner ℂ (laplacian u) (v : ModularHilbert) =
      inner ℂ (closedGradient ⟨u, laplacian_domain_le u.property⟩) (closedGradient v) :=
  closedGradientOperator_representation _ _ _ u v

theorem laplacian_domain_iff (u : closedGradient.domain) :
    (u : ModularHilbert) ∈ laplacian.domain ↔ closedGradient u ∈ closedGradient.adjoint.domain :=
  closedGradientOperator_domain_iff _ _ _ u

theorem laplacian_value (u : closedGradient.domain)
    (hu : closedGradient u ∈ closedGradient.adjoint.domain) :
    laplacian ⟨u, (laplacian_domain_iff u).mpr hu⟩ =
      closedGradient.adjoint ⟨closedGradient u, hu⟩ :=
  closedGradientOperator_value _ _ _ u hu

theorem laplacian_kernel : laplacian.ker = closedGradient.ker :=
  closedGradientOperator_kernel _ _ _

theorem laplacian_domain_eq_resolvent_range : laplacian.domain = weakResolvent.range := rfl

theorem formEmbedding_denseRange : DenseRange formEmbedding := by
  change Dense (Set.range (gradientEmbedding closedGradient))
  rw [gradientEmbedding_range]
  exact closedGradient_dense_domain

theorem weakResolvent_injective : Function.Injective weakResolvent := by
  intro f g hfg
  have hsol : weakSolution f = weakSolution g := formEmbedding_injective hfg
  apply formEmbedding_denseRange.eq_of_inner_left ℂ
  intro v
  rw [← weakSolution_equation f v, ← weakSolution_equation g v, hsol, hfg]

theorem weakResolvent_denseRange : DenseRange weakResolvent := by
  change Dense (weakResolvent.range : Set ModularHilbert)
  rw [← laplacian_domain_eq_resolvent_range]
  exact laplacian_dense_domain

theorem weakResolvent_mem_laplacian_domain (f : ModularHilbert) :
    weakResolvent f ∈ laplacian.domain := by
  rw [laplacian_domain_eq_resolvent_range]
  exact LinearMap.mem_range_self weakResolvent.toLinearMap f

/-- The constructed weak solution is a right inverse of the actual shifted operator. -/
theorem laplacian_resolvent (f : ModularHilbert) :
    laplacian ⟨weakResolvent f, weakResolvent_mem_laplacian_domain f⟩ + weakResolvent f = f := by
  exact inverseShift_apply_range_add weakResolvent weakResolvent_injective f

/-- The same weak solution is a left inverse on the actual operator domain. -/
theorem resolvent_laplacian (u : laplacian.domain) :
    weakResolvent (laplacian u + u) = u := by
  exact inverseShift_image_apply_add weakResolvent weakResolvent_injective u

theorem modularConstant_mem_laplacian_domain : modularConstant ∈ laplacian.domain := by
  apply (laplacian_domain_iff
    ⟨modularConstant, modularConstant_mem_closedGradient_domain⟩).mpr
  rw [closedGradient_modularConstant]
  exact closedGradient.adjoint.domain.zero_mem

theorem laplacian_modularConstant :
    laplacian ⟨modularConstant, modularConstant_mem_laplacian_domain⟩ = 0 := by
  have h := laplacian_value ⟨modularConstant, modularConstant_mem_closedGradient_domain⟩
    (by rw [closedGradient_modularConstant]; exact closedGradient.adjoint.domain.zero_mem)
  have hz : (⟨closedGradient ⟨modularConstant, modularConstant_mem_closedGradient_domain⟩,
      (by rw [closedGradient_modularConstant]; exact closedGradient.adjoint.domain.zero_mem)⟩ :
      closedGradient.adjoint.domain) = 0 := Subtype.ext closedGradient_modularConstant
  simpa only [hz, LinearPMap.map_zero] using h

theorem constantSpace_le_laplacian_kernel : modularConstantSpace ≤ laplacian.ker := by
  rw [laplacian_kernel]
  exact constantSpace_le_closedGradient_kernel

/-- Every operator value has ordinary integral zero. -/
theorem laplacian_integral (u : laplacian.domain) :
    ∫ z, laplacian u z ∂modularMeasure = 0 := by
  have h := laplacian_representation u
    ⟨modularConstant, modularConstant_mem_closedGradient_domain⟩
  rw [closedGradient_modularConstant, inner_zero_right] at h
  rw [← modularConstant_inner]
  exact inner_eq_zero_symm.mp h

theorem laplacian_mem_meanZero (u : laplacian.domain) : laplacian u ∈ modularMeanZero :=
  (mem_modularMeanZero_iff _).mpr (laplacian_integral u)

theorem constantProjection_mem_laplacian_domain (f : ModularHilbert) :
    modularConstantProjection f ∈ laplacian.domain := by
  rw [modularConstantProjection_apply]
  exact laplacian.domain.smul_mem _ modularConstant_mem_laplacian_domain

theorem laplacian_constantProjection (f : ModularHilbert) :
    laplacian ⟨modularConstantProjection f, constantProjection_mem_laplacian_domain f⟩ = 0 := by
  have hsub : (⟨modularConstantProjection f,
      constantProjection_mem_laplacian_domain f⟩ : laplacian.domain) =
      modularAverage f • ⟨modularConstant, modularConstant_mem_laplacian_domain⟩ :=
    Subtype.ext (modularConstantProjection_apply f)
  rw [hsub, LinearPMap.map_smul, laplacian_modularConstant, smul_zero]

theorem meanZeroProjection_mem_laplacian_domain (u : laplacian.domain) :
    modularMeanZeroProjection u ∈ laplacian.domain := by
  rw [modularMeanZeroProjection_eq]
  exact laplacian.domain.sub_mem u.property (constantProjection_mem_laplacian_domain u)

theorem laplacian_meanZeroProjection (u : laplacian.domain) :
    laplacian ⟨modularMeanZeroProjection u, meanZeroProjection_mem_laplacian_domain u⟩ =
      laplacian u := by
  have hsub : (⟨modularMeanZeroProjection u,
      meanZeroProjection_mem_laplacian_domain u⟩ : laplacian.domain) =
      u - ⟨modularConstantProjection u, constantProjection_mem_laplacian_domain u⟩ := by
    apply Subtype.ext
    simp only [modularMeanZeroProjection_eq, sub_apply,
      ContinuousLinearMap.id_apply, Submodule.coe_sub]
  rw [hsub, LinearPMap.map_sub, laplacian_constantProjection, sub_zero]

end GapFamily.Analytic.ModularGradient
