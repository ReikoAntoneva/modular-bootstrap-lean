import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# The actual Dedekind eta denominator

These lemmas retain mathlib's infinite-product eta function.  They expose the
translation law and the squared-norm S/T laws needed when converting modular
completed numerators into the character partition function.
-/

namespace GapFamily.Analytic

set_option backward.isDefEq.respectTransparency.types false

open Complex Function
open scoped Real

/-- Translation of the actual Dedekind eta function by one. -/
theorem eta_add_one (z : ℂ) :
    ModularForm.eta (z + 1) =
      Complex.exp (π * I / 12) * ModularForm.eta z := by
  have hq : Periodic.qParam 1 (z + 1) = Periodic.qParam 1 z := by
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, mul_add, mul_one]
    exact Complex.exp_periodic _
  unfold ModularForm.eta
  simp only [ModularForm.eta_q, hq]
  simp only [Periodic.qParam, Complex.ofReal_ofNat]
  have harg : 2 * (π : ℂ) * I * (z + 1) / 24 =
      π * I / 12 + 2 * π * I * z / 24 := by ring
  rw [harg, Complex.exp_add, mul_assoc]

/-- Eta has no zero on the domain used by the torus partition function. -/
theorem eta_ne_zero (z : UpperHalfPlane) : ModularForm.eta z ≠ 0 :=
  ModularForm.eta_ne_zero z.2

/-- The eta S law, with the principal square-root branch supplied by mathlib. -/
theorem eta_neg_inv (z : UpperHalfPlane) :
    ModularForm.eta (-1 / (z : ℂ)) =
      (Complex.sqrt I)⁻¹ * (Complex.sqrt z * ModularForm.eta z) := by
  exact ModularForm.eta_comp_eq_csqrt_I_inv z.2

/-- The squared eta denominator is strictly positive on the upper half-plane. -/
theorem eta_norm_sq_pos (z : UpperHalfPlane) : 0 < ‖ModularForm.eta z‖ ^ 2 := by
  exact pow_pos (norm_pos_iff.mpr (eta_ne_zero z)) 2

/-- The eta denominator is invariant under T. -/
theorem eta_norm_sq_add_one (z : ℂ) :
    ‖ModularForm.eta (z + 1)‖ ^ 2 = ‖ModularForm.eta z‖ ^ 2 := by
  rw [eta_add_one, norm_mul]
  simp [Complex.norm_exp, Complex.mul_re]

private theorem norm_sqrt_sq (z : ℂ) : ‖Complex.sqrt z‖ ^ 2 = ‖z‖ := by
  rw [← norm_pow, Complex.sqrt, Complex.cpow_ofNat_inv_pow]

/-- The eta denominator transforms by `‖z‖` under S. -/
theorem eta_norm_sq_neg_inv (z : UpperHalfPlane) :
    ‖ModularForm.eta (-1 / (z : ℂ))‖ ^ 2 =
      ‖(z : ℂ)‖ * ‖ModularForm.eta z‖ ^ 2 := by
  rw [eta_neg_inv, norm_mul, norm_inv, norm_mul, mul_pow, mul_pow, inv_pow,
    norm_sqrt_sq, norm_sqrt_sq, Complex.norm_I, inv_one, one_mul]

/-- Eta squared norm under the public modular-group S action. -/
theorem eta_norm_sq_S (z : UpperHalfPlane) :
    ‖ModularForm.eta (ModularGroup.S • z : UpperHalfPlane)‖ ^ 2 =
      ‖(z : ℂ)‖ * ‖ModularForm.eta z‖ ^ 2 := by
  rw [UpperHalfPlane.modular_S_smul]
  simpa [neg_div] using eta_norm_sq_neg_inv z

/-- Eta squared norm under the public modular-group T action. -/
theorem eta_norm_sq_T (z : UpperHalfPlane) :
    ‖ModularForm.eta (ModularGroup.T • z : UpperHalfPlane)‖ ^ 2 =
      ‖ModularForm.eta z‖ ^ 2 := by
  rw [UpperHalfPlane.modular_T_smul]
  simpa [add_comm] using eta_norm_sq_add_one z

/-- The positive modular factor converting reduced completions to torus functions. -/
noncomputable def etaInvariantDenominator (z : UpperHalfPlane) : ℝ :=
  Real.sqrt z.im * ‖ModularForm.eta z‖ ^ 2

theorem etaInvariantDenominator_pos (z : UpperHalfPlane) :
    0 < etaInvariantDenominator z :=
  mul_pos (Real.sqrt_pos.mpr z.im_pos) (eta_norm_sq_pos z)

theorem etaInvariantDenominator_S (z : UpperHalfPlane) :
    etaInvariantDenominator (ModularGroup.S • z) = etaInvariantDenominator z := by
  have him : (ModularGroup.S • z).im = z.im / ‖(z : ℂ)‖ ^ 2 := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [Complex.inv_im, Complex.normSq_eq_norm_sq, neg_div]
  unfold etaInvariantDenominator
  rw [eta_norm_sq_S, him, Real.sqrt_div z.im_pos.le, Real.sqrt_sq (norm_nonneg _)]
  field_simp [norm_ne_zero_iff.mpr z.ne_zero]

theorem etaInvariantDenominator_T (z : UpperHalfPlane) :
    etaInvariantDenominator (ModularGroup.T • z) = etaInvariantDenominator z := by
  unfold etaInvariantDenominator
  rw [eta_norm_sq_T]
  rw [UpperHalfPlane.modular_T_smul]
  simp

end GapFamily.Analytic
