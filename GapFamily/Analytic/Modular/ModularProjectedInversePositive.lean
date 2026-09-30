import GapFamily.Analytic.Modular.ModularFullProjectedResolvent

/-!
# Positivity of the actual projected inverse below one quarter

The projected inverse solves the actual shifted operator equation with the
orthogonal mean-zero source. Testing against its own value gives the real
shifted energy, which is nonnegative by the proved actual quarter gap.
-/

noncomputable section
namespace GapFamily.Analytic.ModularProjected

open ModularGradient

theorem projectedInverse_isPositive_real {a : ℝ} (ha : a < 1 / 4) :
    (projectedWeakResolvent.comp (Ring.inverse (projectedPencil (a : ℂ)))).IsPositive := by
  have hQ : IsUnit (projectedPencil (a : ℂ)) :=
    projectedPencil_isUnit_regular (Or.inr (by simpa only [Complex.ofReal_re] using ha))
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro f
  let x : laplacian.domain :=
    ⟨projectedWeakResolvent (Ring.inverse (projectedPencil (a : ℂ)) f),
      projectedWeakResolvent_mem_domain _⟩
  have hx : (x : ModularHilbert) ∈ modularMeanZero := projectedWeakResolvent_mem_meanZero _
  have hPx : modularMeanZeroProjection (x : ModularHilbert) = x :=
    modularMeanZero.starProjection_eq_self_iff.mpr hx
  have hproj : inner ℂ (x : ModularHilbert) f =
      inner ℂ (x : ModularHilbert) (modularMeanZeroProjection f) := by
    have h := modularMeanZeroProjection_selfAdjoint.isSymmetric (x : ModularHilbert) f
    change inner ℂ (modularMeanZeroProjection (x : ModularHilbert)) f =
      inner ℂ (x : ModularHilbert) (modularMeanZeroProjection f) at h
    simpa only [hPx] using h
  have hshift : laplacian x - (a : ℂ) • (x : ModularHilbert) = modularMeanZeroProjection f :=
    projected_inverse_right_shift hQ f
  have hrep := congrArg (starRingEnd ℂ)
    (laplacian_representation x ⟨x, laplacian_domain_le x.property⟩)
  simp only [inner_conj_symm] at hrep
  have hpair : inner ℂ (x : ModularHilbert) f =
      ((‖closedGradient ⟨x, laplacian_domain_le x.property⟩‖ ^ 2 -
        a * ‖(x : ModularHilbert)‖ ^ 2 : ℝ) : ℂ) := by
    rw [hproj, ← hshift, inner_sub_right, inner_smul_right, hrep,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    norm_num [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow]
  have horth : inner ℂ modularConstant (x : ModularHilbert) = 0 := by
    rw [modularConstant_inner]
    exact (mem_modularMeanZero_iff _).mp hx
  have hgap := form_quarter_mass_le_energy_of_constant_orthogonal
    (formLift ⟨x, laplacian_domain_le x.property⟩) horth
  change (1 / 4 : ℝ) * ‖(x : ModularHilbert)‖ ^ 2 ≤
    ‖closedGradient ⟨x, laplacian_domain_le x.property⟩‖ ^ 2 at hgap
  change (((inner ℂ (x : ModularHilbert) f).re : ℝ) : ℂ) =
      inner ℂ (x : ModularHilbert) f ∧ 0 ≤ (inner ℂ (x : ModularHilbert) f).re
  rw [hpair]
  simp only [Complex.ofReal_re]
  refine ⟨trivial, ?_⟩
  have hnonneg := mul_nonneg (sub_nonneg.mpr ha.le) (sq_nonneg ‖(x : ModularHilbert)‖)
  nlinarith

end GapFamily.Analytic.ModularProjected
