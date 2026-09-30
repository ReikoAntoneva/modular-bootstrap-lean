import GapFamily.Analytic.Modular.ModularPositiveResolventBasic

/-! Positivity and contraction of the genuine negative-parameter modular
resolvent, proved through the actual unbounded Laplacian domain and energy. -/

noncomputable section
namespace GapFamily.Analytic.ModularPositiveResolvent
open ModularGradient

/-- Symmetry follows by testing the two actual domain inverse equations. -/
theorem shiftedResolvent_isSymmetric (r : ℝ) (hr : 0 < r) :
    (shiftedResolvent r).IsSymmetric := by
  intro f g
  let u : laplacian.domain := ⟨shiftedResolvent r f, shiftedResolvent_mem_domain r f⟩
  let v : laplacian.domain := ⟨shiftedResolvent r g, shiftedResolvent_mem_domain r g⟩
  have hu : laplacian u + (r : ℂ) • (u : ModularHilbert) = f :=
    shiftedResolvent_rightInverse r hr f
  have hv : laplacian v + (r : ℂ) • (v : ModularHilbert) = g :=
    shiftedResolvent_rightInverse r hr g
  change inner ℂ (u : ModularHilbert) g = inner ℂ f (v : ModularHilbert)
  calc
    _ = inner ℂ (u : ModularHilbert)
        (laplacian v + (r : ℂ) • (v : ModularHilbert)) := by rw [hv]
    _ = inner ℂ (laplacian u + (r : ℂ) • (u : ModularHilbert))
        (v : ModularHilbert) := by
      simp only [inner_add_right, inner_add_left, inner_smul_right, inner_smul_left,
        Complex.conj_ofReal, laplacian_inner_symm]
    _ = inner ℂ f (v : ModularHilbert) := by rw [hu]

/-- The actual nonnegative Laplacian energy supplies the coercive lower bound. -/
private theorem shiftedResolvent_coercive (r : ℝ) (hr : 0 < r) (f : ModularHilbert) :
    r * ‖shiftedResolvent r f‖ ^ 2 ≤ (inner ℂ (shiftedResolvent r f) f).re := by
  let u : laplacian.domain := ⟨shiftedResolvent r f, shiftedResolvent_mem_domain r f⟩
  have hu : laplacian u + (r : ℂ) • (u : ModularHilbert) = f :=
    shiftedResolvent_rightInverse r hr f
  have hpair : inner ℂ (u : ModularHilbert) f =
      inner ℂ (laplacian u) (u : ModularHilbert) +
        (r : ℂ) * ((‖(u : ModularHilbert)‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = inner ℂ (u : ModularHilbert)
          (laplacian u + (r : ℂ) • (u : ModularHilbert)) := by rw [hu]
      _ = _ := by
        rw [inner_add_right, inner_smul_right, ← laplacian_inner_symm u u,
          inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
        rfl
  change r * ‖(u : ModularHilbert)‖ ^ 2 ≤ (inner ℂ (u : ModularHilbert) f).re
  rw [hpair]
  simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using
    le_add_of_nonneg_left (laplacian_nonnegative u)

/-- The actual full shifted modular resolvent is a positive bounded operator. -/
theorem shiftedResolvent_isPositive (r : ℝ) (hr : 0 < r) :
    (shiftedResolvent r).IsPositive := by
  refine ⟨shiftedResolvent_isSymmetric r hr, fun f => ?_⟩
  change 0 ≤ (inner ℂ (shiftedResolvent r f) f).re
  exact (mul_nonneg hr.le (sq_nonneg _)).trans (shiftedResolvent_coercive r hr f)

theorem shiftedResolvent_isSelfAdjoint (r : ℝ) (hr : 0 < r) :
    IsSelfAdjoint (shiftedResolvent r) := (shiftedResolvent_isPositive r hr).isSelfAdjoint

theorem resolventFactor_isPositive (r : ℝ) (hr : 0 < r) :
    (resolventFactor r).IsPositive :=
  (shiftedResolvent_isPositive r hr).smul_of_nonneg ((RCLike.ofReal_nonneg (K := ℂ)).mpr hr.le)

theorem resolventFactor_isSelfAdjoint (r : ℝ) (hr : 0 < r) :
    IsSelfAdjoint (resolventFactor r) := (resolventFactor_isPositive r hr).isSelfAdjoint

/-- Coercivity and Cauchy–Schwarz give the exact normalized contraction bound. -/
theorem resolventFactor_norm_le_one (r : ℝ) (hr : 0 < r) :
    ‖resolventFactor r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have hc := (shiftedResolvent_coercive r hr f).trans
    (Complex.re_le_norm (inner ℂ (shiftedResolvent r f) f))
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (shiftedResolvent r f) f
  have hbound : r * ‖shiftedResolvent r f‖ ≤ ‖f‖ := by
    by_cases hu : shiftedResolvent r f = 0
    · simp [hu]
    · apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hu)).mp
      nlinarith only [hc, hcs]
  calc
    ‖resolventFactor r f‖ = r * ‖shiftedResolvent r f‖ := by
      simp only [resolventFactor, smul_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg hr.le]
    _ ≤ ‖f‖ := hbound
    _ = 1 * ‖f‖ := (one_mul _).symm

end GapFamily.Analytic.ModularPositiveResolvent
