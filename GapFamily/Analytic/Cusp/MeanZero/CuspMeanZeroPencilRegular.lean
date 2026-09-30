import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroPencilBasic
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroCoercive

/-!
# Regular parameter of the actual constrained pencil

The actual compact positive cusp-average-zero response has no pencil
singularity off the real axis or in the closed left half-plane. The proof uses
the literal response quadratic form and its proved strict norm bound, followed
by the compact Fredholm alternative. No spectral completeness or ambient
constrained-density hypothesis is used.
-/

noncomputable section

namespace GapFamily.Analytic

private theorem cuspMeanZeroPencil_isUnit_of_no_fixed (z : ℂ)
    (hfixed : ∀ f : ModularHilbert, ((z + 1) • cuspMeanZeroWeakResolvent) f = f → f = 0) :
    IsUnit (cuspMeanZeroPencil z) := by
  have hcompact : IsCompactOperator
      ((z + 1) • cuspMeanZeroWeakResolvent : ModularHilbert →L[ℂ] ModularHilbert) :=
    cuspMeanZeroWeakResolvent_isCompact.smul (z + 1)
  have hnoEigen : ¬ Module.End.HasEigenvalue
      (((z + 1) • cuspMeanZeroWeakResolvent) : ModularHilbert →ₗ[ℂ] ModularHilbert) 1 := by
    intro heigen
    obtain ⟨f, hf⟩ := heigen.exists_hasEigenvector
    exact hf.2 (hfixed f (by simpa using hf.apply_eq_smul))
  have hres : (1 : ℂ) ∈ resolventSet ℂ
      ((z + 1) • cuspMeanZeroWeakResolvent : ModularHilbert →L[ℂ] ModularHilbert) :=
    (hcompact.hasEigenvalue_or_mem_resolventSet one_ne_zero).resolve_left hnoEigen
  simpa only [spectrum.mem_resolventSet_iff, map_one, cuspMeanZeroPencil,
    compactSelfAdjointPencil] using hres

private theorem cuspMeanZero_scaled_fixed_inner (z : ℂ) (f : ModularHilbert)
    (hf : ((z + 1) • cuspMeanZeroWeakResolvent) f = f) :
    (z + 1) * inner ℂ f (cuspMeanZeroWeakResolvent f) = inner ℂ f f := by
  calc
    (z + 1) * inner ℂ f (cuspMeanZeroWeakResolvent f) =
        inner ℂ f (((z + 1) • cuspMeanZeroWeakResolvent) f) := by
      simp only [smul_apply, inner_smul_right]
    _ = inner ℂ f f := by rw [hf]

/-- Every nonreal parameter is regular for the actual constrained pencil. -/
theorem cuspMeanZeroPencil_isUnit_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) :
    IsUnit (cuspMeanZeroPencil z) := by
  apply cuspMeanZeroPencil_isUnit_of_no_fixed z
  intro f hf
  have him : (inner ℂ f (cuspMeanZeroWeakResolvent f)).im = 0 :=
    cuspMeanZeroWeakResolvent_isPositive.isSymmetric.im_inner_self_apply f
  have hq := cuspMeanZero_scaled_fixed_inner z f hf
  have hselfim : (inner ℂ f f).im = 0 := inner_self_im (𝕜 := ℂ) f
  have hselfre : (inner ℂ f f).re = ‖f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
  have hi : z.im * (inner ℂ f (cuspMeanZeroWeakResolvent f)).re = 0 := by
    simpa only [Complex.mul_im, Complex.add_im, Complex.one_im, add_zero,
      him, mul_zero, zero_add, hselfim] using congrArg Complex.im hq
  have hp : (inner ℂ f (cuspMeanZeroWeakResolvent f)).re = 0 :=
    (mul_eq_zero.mp hi).resolve_left hz
  have hre : ‖f‖ ^ 2 = 0 := by
    simpa only [Complex.mul_re, him, hp, mul_zero, sub_zero, hselfre] using
      (congrArg Complex.re hq).symm
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hre)

/-- The entire closed left half-plane is regular for the actual constrained pencil. -/
theorem cuspMeanZeroPencil_isUnit_of_re_nonpos (z : ℂ) (hz : z.re ≤ 0) :
    IsUnit (cuspMeanZeroPencil z) := by
  apply cuspMeanZeroPencil_isUnit_of_no_fixed z
  intro f hf
  have him : (inner ℂ f (cuspMeanZeroWeakResolvent f)).im = 0 :=
    cuspMeanZeroWeakResolvent_isPositive.isSymmetric.im_inner_self_apply f
  have hq := cuspMeanZero_scaled_fixed_inner z f hf
  have hselfre : (inner ℂ f f).re = ‖f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
  have hre : (z.re + 1) * (inner ℂ f (cuspMeanZeroWeakResolvent f)).re = ‖f‖ ^ 2 := by
    simpa only [Complex.mul_re, Complex.add_re, Complex.one_re, him,
      mul_zero, sub_zero, hselfre] using congrArg Complex.re hq
  have hp : 0 ≤ (inner ℂ f (cuspMeanZeroWeakResolvent f)).re :=
    cuspMeanZeroWeakResolvent_isPositive.re_inner_nonneg_right f
  have hfactor : z.re + 1 ≤ 1 := by linarith
  have hmass : ‖f‖ ^ 2 ≤ (inner ℂ f (cuspMeanZeroWeakResolvent f)).re := by
    rw [← hre]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor hp
  have hc := re_inner_le_norm (𝕜 := ℂ) f (cuspMeanZeroWeakResolvent f)
  change (inner ℂ f (cuspMeanZeroWeakResolvent f)).re ≤
    ‖f‖ * ‖cuspMeanZeroWeakResolvent f‖ at hc
  have hop := mul_le_mul_of_nonneg_left (cuspMeanZeroWeakResolvent.le_opNorm f)
    (norm_nonneg f)
  have hstrict := cuspMeanZeroWeakResolvent_norm_lt_one
  have hbound : ‖f‖ ^ 2 ≤ ‖cuspMeanZeroWeakResolvent‖ * ‖f‖ ^ 2 := calc
    ‖f‖ ^ 2 ≤ (inner ℂ f (cuspMeanZeroWeakResolvent f)).re := hmass
    _ ≤ ‖f‖ * ‖cuspMeanZeroWeakResolvent f‖ := hc
    _ ≤ ‖f‖ * (‖cuspMeanZeroWeakResolvent‖ * ‖f‖) := hop
    _ = ‖cuspMeanZeroWeakResolvent‖ * ‖f‖ ^ 2 := by ring
  by_contra hnonzero
  have hpos : 0 < ‖f‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hnonzero)
  have hlt := mul_lt_mul_of_pos_right hstrict hpos
  nlinarith only [hbound, hlt]

/-- In particular every nonpositive real spectral parameter is regular. -/
theorem cuspMeanZeroPencil_isUnit_of_real_nonpos (t : ℝ) (ht : t ≤ 0) :
    IsUnit (cuspMeanZeroPencil (t : ℂ)) :=
  cuspMeanZeroPencil_isUnit_of_re_nonpos t ht

/-- Every singular parameter of the actual constrained pencil is positive real. -/
theorem cuspMeanZeroPencil_nonunit_real_pos (z : ℂ)
    (hz : ¬ IsUnit (cuspMeanZeroPencil z)) : z.im = 0 ∧ 0 < z.re := by
  constructor
  · by_contra him
    exact hz (cuspMeanZeroPencil_isUnit_of_im_ne_zero z him)
  · by_contra! hre
    exact hz (cuspMeanZeroPencil_isUnit_of_re_nonpos z hre)

end GapFamily.Analytic
