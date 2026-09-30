import GapFamily.Analytic.Modular.ModularVolume
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The modular Hilbert space and its constant channel

The space is the actual complex `L²` space for hyperbolic measure restricted
to the standard modular fundamental domain. The constant channel is an
orthogonal projection with an ordinary integral formula.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set
open scoped ComplexConjugate

/-- The spectral Hilbert space with hyperbolic measure on the fundamental domain. -/
abbrev ModularHilbert := Lp ℂ 2 modularMeasure

/-- The constant function one as an actual `L²` vector. -/
def modularConstant : ModularHilbert :=
  (memLp_const (μ := modularMeasure) (p := 2) (1 : ℂ)).toLp (fun _ => 1)

theorem modularConstant_ae : modularConstant =ᵐ[modularMeasure] fun _ => (1 : ℂ) :=
  MemLp.coeFn_toLp _

/-- The inner product against the constant vector is the ordinary integral. -/
theorem modularConstant_inner (f : ModularHilbert) :
    inner ℂ modularConstant f = ∫ z, f z ∂modularMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [modularConstant_ae] with z hz
  simp [hz]

theorem integrable_modularHilbert (f : ModularHilbert) :
    Integrable f modularMeasure := by
  apply (L2.integrable_inner (𝕜 := ℂ) modularConstant f).congr
  filter_upwards [modularConstant_ae] with z hz
  simp [hz]

theorem modularConstant_inner_self :
    inner ℂ modularConstant modularConstant = (modularMeasure.real univ : ℂ) := by
  rw [modularConstant_inner, integral_congr_ae modularConstant_ae]
  simp

theorem modularConstant_norm_sq : ‖modularConstant‖ ^ 2 = modularMeasure.real univ := by
  calc
    ‖modularConstant‖ ^ 2 = (inner ℂ modularConstant modularConstant).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) modularConstant
    _ = modularMeasure.real univ := by rw [modularConstant_inner_self]; rfl

theorem modularConstant_ne_zero : modularConstant ≠ 0 := by
  intro h
  have hn := modularConstant_norm_sq
  rw [h, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hn
  exact modularMeasure_real_univ_pos.ne' hn.symm

theorem modularConstant_norm : ‖modularConstant‖ = Real.sqrt (modularMeasure.real univ) := by
  rw [← modularConstant_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The normalized constant spectral vector. -/
def modularUnitConstant : ModularHilbert :=
  (Real.sqrt (modularMeasure.real univ) : ℂ)⁻¹ • modularConstant

theorem modularUnitConstant_ae :
    modularUnitConstant =ᵐ[modularMeasure]
      fun _ => (Real.sqrt (modularMeasure.real univ) : ℂ)⁻¹ := by
  unfold modularUnitConstant
  filter_upwards [Lp.coeFn_smul (Real.sqrt (modularMeasure.real univ) : ℂ)⁻¹
    modularConstant, modularConstant_ae] with z hz hc
  simp [hz, hc]

theorem modularUnitConstant_norm : ‖modularUnitConstant‖ = 1 := by
  rw [modularUnitConstant, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), modularConstant_norm,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr modularMeasure_real_univ_pos).ne']

/-- The actual average is a bounded linear functional. -/
def modularAverage : ModularHilbert →L[ℂ] ℂ :=
  (modularMeasure.real univ : ℂ)⁻¹ • innerSL ℂ modularConstant

theorem modularAverage_apply (f : ModularHilbert) :
    modularAverage f = (∫ z, f z ∂modularMeasure) / modularMeasure.real univ := by
  simp [modularAverage, modularConstant_inner, div_eq_mul_inv, mul_comm]

theorem modularAverage_constant : modularAverage modularConstant = 1 := by
  have hm : (modularMeasure.real univ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr modularMeasure_real_univ_pos.ne'
  change (modularMeasure.real univ : ℂ)⁻¹ * inner ℂ modularConstant modularConstant = 1
  rw [modularConstant_inner_self, inv_mul_cancel₀ hm]

/-- Constants as a closed one-dimensional subspace. -/
def modularConstantSpace : Submodule ℂ ModularHilbert := ℂ ∙ modularConstant

instance : FiniteDimensional ℂ modularConstantSpace :=
  inferInstanceAs (FiniteDimensional ℂ (ℂ ∙ modularConstant))

/-- Orthogonal projection onto the actual constant channel. -/
def modularConstantProjection : ModularHilbert →L[ℂ] ModularHilbert :=
  modularConstantSpace.starProjection

theorem modularConstantProjection_apply (f : ModularHilbert) :
    modularConstantProjection f = modularAverage f • modularConstant := by
  change (ℂ ∙ modularConstant).starProjection f = _
  rw [Submodule.starProjection_singleton, modularConstant_norm_sq,
    modularConstant_inner, modularAverage_apply]
  rfl

theorem modularConstantProjection_ae (f : ModularHilbert) :
    modularConstantProjection f =ᵐ[modularMeasure] fun _ => modularAverage f := by
  rw [modularConstantProjection_apply]
  filter_upwards [Lp.coeFn_smul (modularAverage f) modularConstant,
    modularConstant_ae] with z hz hc
  simp [hz, hc]

/-- The integral kernel of the orthogonal constant projection. -/
def modularConstantKernel (_z _w : UpperHalfPlane) : ℂ :=
  (modularMeasure.real univ : ℂ)⁻¹

theorem modularConstantKernel_eq (z w : UpperHalfPlane) :
    modularConstantKernel z w = 3 / (Real.pi : ℂ) := by
  rw [modularConstantKernel, modularMeasure_real_univ]
  push_cast
  field_simp

/-- Arithmetic normalization of the constant spectral channel. The multiplier
`-2π` must still be obtained from the actual spatial spectral calculation. -/
theorem modularConstantKernel_normalization (z w : UpperHalfPlane) :
    (-2 * (Real.pi : ℂ)) * modularConstantKernel z w = -6 := by
  rw [modularConstantKernel_eq]
  field_simp
  norm_num

theorem modularConstantKernel_integrable (z : UpperHalfPlane) (f : ModularHilbert) :
    Integrable (fun w => modularConstantKernel z w * f w) modularMeasure :=
  (integrable_modularHilbert f).const_mul _

theorem modularConstantKernel_integral (z : UpperHalfPlane) (f : ModularHilbert) :
    (∫ w, modularConstantKernel z w * f w ∂modularMeasure) = modularAverage f := by
  change (∫ w, (modularMeasure.real univ : ℂ)⁻¹ * f w ∂modularMeasure) = _
  rw [integral_const_mul, modularAverage_apply, div_eq_mul_inv, mul_comm]

theorem modularConstantProjection_kernel (f : ModularHilbert) :
    modularConstantProjection f =ᵐ[modularMeasure]
      fun z => ∫ w, modularConstantKernel z w * f w ∂modularMeasure := by
  simpa only [modularConstantKernel_integral] using modularConstantProjection_ae f

/-- Almost-everywhere factorization by the actual normalized constant vector. -/
theorem modularConstantKernel_unitFactor :
    ∀ᵐ z ∂modularMeasure, ∀ᵐ w ∂modularMeasure,
      modularConstantKernel z w = modularUnitConstant z * conj (modularUnitConstant w) := by
  have hsq : ((Real.sqrt (modularMeasure.real univ) : ℂ) ^ 2) =
      (modularMeasure.real univ : ℂ) := by
    norm_cast
    exact Real.sq_sqrt modularMeasure_real_univ_pos.le
  filter_upwards [modularUnitConstant_ae] with z hz
  filter_upwards [modularUnitConstant_ae] with w hw
  simp only [hz, hw, modularConstantKernel, map_inv₀, Complex.conj_ofReal]
  rw [← mul_inv, ← pow_two, hsq]

theorem modularConstantProjection_idempotent :
    IsIdempotentElem modularConstantProjection :=
  modularConstantSpace.isIdempotentElem_starProjection

theorem modularConstantProjection_selfAdjoint :
    IsSelfAdjoint modularConstantProjection :=
  isSelfAdjoint_starProjection modularConstantSpace

theorem modularConstantProjection_norm : ‖modularConstantProjection‖ = 1 := by
  apply modularConstantSpace.norm_starProjection
  simpa [modularConstantSpace] using modularConstant_ne_zero

/-- The mean-zero spectral subspace. -/
def modularMeanZero : Submodule ℂ ModularHilbert := modularConstantSpaceᗮ

instance : modularMeanZero.HasOrthogonalProjection :=
  inferInstanceAs modularConstantSpaceᗮ.HasOrthogonalProjection

theorem mem_modularMeanZero_iff (f : ModularHilbert) :
    f ∈ modularMeanZero ↔ ∫ z, f z ∂modularMeasure = 0 := by
  rw [modularMeanZero, modularConstantSpace,
    Submodule.mem_orthogonal_singleton_iff_inner_right, modularConstant_inner]

theorem modularMeanZero_isClosed : IsClosed (modularMeanZero : Set ModularHilbert) :=
  modularConstantSpace.isClosed_orthogonal

theorem modularConstantProjection_eq_zero_iff (f : ModularHilbert) :
    modularConstantProjection f = 0 ↔ ∫ z, f z ∂modularMeasure = 0 := by
  rw [modularConstantProjection, Submodule.starProjection_apply_eq_zero_iff]
  exact mem_modularMeanZero_iff f

theorem modularMeanZero_sub_projection (f : ModularHilbert) :
    f - modularConstantProjection f ∈ modularMeanZero :=
  modularConstantSpace.sub_starProjection_mem_orthogonal f

/-- The complementary, mean-zero orthogonal projection. -/
def modularMeanZeroProjection : ModularHilbert →L[ℂ] ModularHilbert :=
  modularMeanZero.starProjection

theorem modularMeanZeroProjection_eq :
    modularMeanZeroProjection = ContinuousLinearMap.id ℂ ModularHilbert -
      modularConstantProjection := by
  have h := modularConstantSpace.id_eq_sum_starProjection_self_orthogonalComplement
  change ContinuousLinearMap.id ℂ ModularHilbert =
    modularConstantProjection + modularMeanZeroProjection at h
  rw [h, add_sub_cancel_left]

theorem modularMeanZeroProjection_norm_le : ‖modularMeanZeroProjection‖ ≤ 1 :=
  modularMeanZero.starProjection_norm_le

theorem modularMeanZeroProjection_selfAdjoint : IsSelfAdjoint modularMeanZeroProjection :=
  isSelfAdjoint_starProjection modularMeanZero

theorem modularMeanZeroProjection_integral (f : ModularHilbert) :
    ∫ z, modularMeanZeroProjection f z ∂modularMeasure = 0 := by
  apply (mem_modularMeanZero_iff _).mp
  exact (modularMeanZero.orthogonalProjectionOnto f).property

end GapFamily.Analytic
