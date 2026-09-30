import GapFamily.Analytic.Modular.ModularProjectedPencilInverse

/-!
# Actual full modular resolvent from the projected response

The constant-orthogonal response supplies the mean-zero inverse. The exact
constant-channel term is -z⁻¹ times the actual constant projection. Domain
membership and both inverse identities use the actual modular Laplacian.
-/

noncomputable section
namespace GapFamily.Analytic.ModularProjected
open ModularGradient

theorem projectedWeakResolvent_mem_domain (f : ModularHilbert) :
    projectedWeakResolvent f ∈ laplacian.domain := by
  rw [projectedWeakResolvent_eq_sub_constantProjection]
  exact laplacian.domain.sub_mem (weakResolvent_mem_laplacian_domain f)
    (constantProjection_mem_laplacian_domain f)

theorem laplacian_projectedWeakResolvent_add (f : ModularHilbert) :
    laplacian ⟨projectedWeakResolvent f, projectedWeakResolvent_mem_domain f⟩ +
      projectedWeakResolvent f = modularMeanZeroProjection f := by
  have hp : (⟨projectedWeakResolvent f, projectedWeakResolvent_mem_domain f⟩ :
      laplacian.domain) =
      ⟨weakResolvent f, weakResolvent_mem_laplacian_domain f⟩ -
        ⟨modularConstantProjection f, constantProjection_mem_laplacian_domain f⟩ :=
    Subtype.ext (projectedWeakResolvent_eq_sub_constantProjection f)
  rw [hp, LinearPMap.map_sub, laplacian_constantProjection, sub_zero,
    projectedWeakResolvent_eq_sub_constantProjection, modularMeanZeroProjection_eq,
    sub_apply, ContinuousLinearMap.id_apply]
  have h := laplacian_resolvent f
  calc
    _ = (laplacian ⟨weakResolvent f, weakResolvent_mem_laplacian_domain f⟩ +
      weakResolvent f) - modularConstantProjection f := by abel
    _ = f - modularConstantProjection f := by rw [h]

/-- The literal bounded ambient candidate; inverse identities require actual pencil regularity and z≠0. -/
def fullResolvent (z : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  projectedWeakResolvent.comp (Ring.inverse (projectedPencil z)) -
    z⁻¹ • modularConstantProjection

@[simp] theorem fullResolvent_apply (z : ℂ) (f : ModularHilbert) :
    fullResolvent z f = projectedWeakResolvent (Ring.inverse (projectedPencil z) f) -
      z⁻¹ • modularConstantProjection f := rfl

/-- The totalized candidate always lies in the actual operator domain. -/
theorem fullResolvent_mem_domain (z : ℂ) (f : ModularHilbert) :
    fullResolvent z f ∈ laplacian.domain := by
  rw [fullResolvent_apply]
  exact laplacian.domain.sub_mem (projectedWeakResolvent_mem_domain _)
    (laplacian.domain.smul_mem _ (constantProjection_mem_laplacian_domain f))

theorem laplacian_fullResolvent (z : ℂ) (f : ModularHilbert) :
    laplacian ⟨fullResolvent z f, fullResolvent_mem_domain z f⟩ =
      laplacian ⟨projectedWeakResolvent (Ring.inverse (projectedPencil z) f),
        projectedWeakResolvent_mem_domain _⟩ := by
  have hp : (⟨fullResolvent z f, fullResolvent_mem_domain z f⟩ : laplacian.domain) =
      ⟨projectedWeakResolvent (Ring.inverse (projectedPencil z) f),
        projectedWeakResolvent_mem_domain _⟩ -
      z⁻¹ • ⟨modularConstantProjection f, constantProjection_mem_laplacian_domain f⟩ :=
    Subtype.ext (fullResolvent_apply z f)
  rw [hp, LinearPMap.map_sub, LinearPMap.map_smul,
    laplacian_constantProjection, smul_zero, sub_zero]

/-- The projected inverse has the actual projected source as right-hand side. -/
theorem projected_inverse_right_shift {z : ℂ} (hQ : IsUnit (projectedPencil z))
    (f : ModularHilbert) :
    laplacian ⟨projectedWeakResolvent (Ring.inverse (projectedPencil z) f),
        projectedWeakResolvent_mem_domain _⟩ -
      z • projectedWeakResolvent (Ring.inverse (projectedPencil z) f) =
        modularMeanZeroProjection f := by
  let g := Ring.inverse (projectedPencil z) f
  have he := laplacian_projectedWeakResolvent_add g
  have hQeq : g - (z + 1) • projectedWeakResolvent g = f := projectedPencil_apply_inverse hQ f
  have hC : modularConstantProjection g = modularConstantProjection f :=
    constantProjection_pencil_inverse hQ f
  rw [modularMeanZeroProjection_eq, sub_apply,
    ContinuousLinearMap.id_apply, hC] at he
  change laplacian ⟨projectedWeakResolvent g, projectedWeakResolvent_mem_domain g⟩ -
    z • projectedWeakResolvent g = _
  calc
    _ = (laplacian ⟨projectedWeakResolvent g, projectedWeakResolvent_mem_domain g⟩ +
        projectedWeakResolvent g) - (z + 1) • projectedWeakResolvent g := by module
    _ = (g - modularConstantProjection f) - (z + 1) • projectedWeakResolvent g := by rw [he]
    _ = f - modularConstantProjection f := by rw [← hQeq]; abel
    _ = modularMeanZeroProjection f := by
      rw [modularMeanZeroProjection_eq]
      rfl

/-- The exact constant term restores the full source with the sign of A-z. -/
theorem fullResolvent_rightInverse_of_isUnit {z : ℂ}
    (hQ : IsUnit (projectedPencil z)) (hz : z ≠ 0) (f : ModularHilbert) :
    laplacian ⟨fullResolvent z f, fullResolvent_mem_domain z f⟩ - z • fullResolvent z f = f := by
  rw [laplacian_fullResolvent, fullResolvent_apply, smul_sub, smul_smul,
    mul_inv_cancel₀ hz, one_smul]
  have h := projected_inverse_right_shift hQ f
  calc
    _ = (laplacian ⟨projectedWeakResolvent (Ring.inverse (projectedPencil z) f),
          projectedWeakResolvent_mem_domain _⟩ -
        z • projectedWeakResolvent (Ring.inverse (projectedPencil z) f)) +
          modularConstantProjection f := by abel
    _ = modularMeanZeroProjection f + modularConstantProjection f := by rw [h]
    _ = f := by
      rw [modularMeanZeroProjection_eq, sub_apply,
        ContinuousLinearMap.id_apply, sub_add_cancel]

theorem constantProjection_laplacian (x : laplacian.domain) :
    modularConstantProjection (laplacian x) = 0 :=
  (modularConstantProjection_eq_zero_iff _).mpr (laplacian_integral x)

/-- The projected part is a left inverse on every vector of the actual full operator domain. -/
theorem projected_inverse_left_shift {z : ℂ} (hQ : IsUnit (projectedPencil z))
    (x : laplacian.domain) :
    projectedWeakResolvent (Ring.inverse (projectedPencil z)
      (laplacian x - z • (x : ModularHilbert))) = modularMeanZeroProjection x := by
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hQ).1
  rw [projectedPencil_commutes_response, projectedPencil_apply_inverse hQ,
    projectedPencil_apply, projectedWeakResolvent_projection]
  have hshift : projectedWeakResolvent (laplacian x + (x : ModularHilbert)) =
      modularMeanZeroProjection x := by
    rw [projectedWeakResolvent_apply, resolvent_laplacian]
  rw [show laplacian x - z • (x : ModularHilbert) =
      (laplacian x + (x : ModularHilbert)) - (z + 1) • (x : ModularHilbert) by module,
    map_sub, map_smul, hshift]

/-- The same bounded ambient map is a left inverse of A-z on its actual domain. -/
theorem fullResolvent_leftInverse_of_isUnit {z : ℂ}
    (hQ : IsUnit (projectedPencil z)) (hz : z ≠ 0) (x : laplacian.domain) :
    fullResolvent z (laplacian x - z • (x : ModularHilbert)) = x := by
  rw [fullResolvent_apply, projected_inverse_left_shift hQ,
    map_sub, map_smul, constantProjection_laplacian, zero_sub,
    smul_neg, smul_smul, inv_mul_cancel₀ hz, one_smul, sub_neg_eq_add,
    modularMeanZeroProjection_eq, sub_apply,
    ContinuousLinearMap.id_apply, sub_add_cancel]

/-- Actual full right inverse outside the quarter ray and away from the constant eigenvalue. -/
theorem fullResolvent_rightInverse {z : ℂ} (hz : z ≠ 0)
    (hreg : z.im ≠ 0 ∨ z.re < (1 / 4 : ℝ)) (f : ModularHilbert) :
    laplacian ⟨fullResolvent z f, fullResolvent_mem_domain z f⟩ - z • fullResolvent z f = f :=
  fullResolvent_rightInverse_of_isUnit (projectedPencil_isUnit_regular hreg) hz f

theorem fullResolvent_leftInverse {z : ℂ} (hz : z ≠ 0)
    (hreg : z.im ≠ 0 ∨ z.re < (1 / 4 : ℝ)) (x : laplacian.domain) :
    fullResolvent z (laplacian x - z • (x : ModularHilbert)) = x :=
  fullResolvent_leftInverse_of_isUnit (projectedPencil_isUnit_regular hreg) hz x

/-- The coefficient on the actual constant channel has the sign of (A-z)⁻¹. -/
theorem fullResolvent_constant {z : ℂ} (hQ : IsUnit (projectedPencil z)) :
    fullResolvent z modularConstant = -(z⁻¹) • modularConstant := by
  rw [fullResolvent_apply, projected_response_inverse_commute hQ,
    projectedWeakResolvent_constant, map_zero, modularConstantProjection_apply,
    modularAverage_constant, one_smul, zero_sub, neg_smul]

/-- The full map recovers the original shifted Riesz resolvent at z=-1. -/
theorem fullResolvent_neg_one : fullResolvent (-1) = weakResolvent := by
  apply ContinuousLinearMap.ext
  intro f
  have hQ : projectedPencil (-1) = 1 := compactSelfAdjointPencil_neg_one projectedWeakResolvent
  rw [fullResolvent_apply, hQ, Ring.inverse_one]
  change projectedWeakResolvent f - (-1 : ℂ)⁻¹ • modularConstantProjection f = weakResolvent f
  rw [projectedWeakResolvent_eq_sub_constantProjection]
  norm_num

/-- The only zero spectral parameter in the physical half-plane is κ=1/2. -/
theorem physical_parameter_ne_zero {κ : ℂ} (hκ : 0 < κ.re) (hhalf : κ ≠ (1 / 2 : ℂ)) :
    (1 / 4 : ℂ) - κ ^ 2 ≠ 0 := by
  have hp : κ + (1 / 2 : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  rw [show (1 / 4 : ℂ) - κ ^ 2 = (1 / 2 - κ) * (κ + 1 / 2) by ring]
  exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hhalf)) hp

/-- The full physical inverse holds throughout Reκ>0 away from the constant pole. -/
theorem fullResolvent_rightInverse_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) :
    laplacian ⟨fullResolvent ((1 / 4 : ℂ) - κ ^ 2) f,
      fullResolvent_mem_domain _ f⟩ -
      ((1 / 4 : ℂ) - κ ^ 2) • fullResolvent ((1 / 4 : ℂ) - κ ^ 2) f = f :=
  fullResolvent_rightInverse_of_isUnit (projectedPencil_isUnit_physical hκ)
    (physical_parameter_ne_zero hκ hhalf) f

theorem fullResolvent_leftInverse_physical {κ : ℂ} (hκ : 0 < κ.re)
    (hhalf : κ ≠ (1 / 2 : ℂ)) (x : laplacian.domain) :
    fullResolvent ((1 / 4 : ℂ) - κ ^ 2)
      (laplacian x - ((1 / 4 : ℂ) - κ ^ 2) • (x : ModularHilbert)) = x :=
  fullResolvent_leftInverse_of_isUnit (projectedPencil_isUnit_physical hκ)
    (physical_parameter_ne_zero hκ hhalf) x

end GapFamily.Analytic.ModularProjected
