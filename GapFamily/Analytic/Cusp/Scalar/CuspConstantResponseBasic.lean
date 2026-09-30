import GapFamily.Analytic.Cusp.Green.CuspGreenAnalytic
import Mathlib.Analysis.Complex.RealDeriv

/-! The actual scalar constant-source profile, with its removable physical value. -/
noncomputable section
namespace GapFamily.Analytic
open Set Filter
open scoped Topology

/-- The removable logarithmic response to the genuine source exp(-t/2).
The remaining denominator has its actual pole at κ=-1/2. -/
def cuspConstantLogResponse (κ : ℂ) (t : ℝ) : ℂ :=
  -dslope (fun z : ℂ => Complex.exp (-z * (t : ℂ))) (1 / 2) κ / (κ + 1 / 2)

theorem cuspConstant_add_half_ne_zero {κ : ℂ} (hκ : κ ≠ -(1 / 2 : ℂ)) :
    κ + 1 / 2 ≠ 0 := by
  intro h
  apply hκ
  linear_combination h

theorem cuspConstant_denominator_ne_zero {κ : ℂ}
    (hp : κ ≠ (1 / 2 : ℂ)) (hm : κ ≠ -(1 / 2 : ℂ)) : (1 / 4 : ℂ) - κ ^ 2 ≠ 0 := by
  have he : (1 / 4 : ℂ) - κ ^ 2 = ((1 / 2 : ℂ) - κ) * (κ + 1 / 2) := by ring
  rw [he]
  exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hp)) (cuspConstant_add_half_ne_zero hm)

/-- Agreement with the explicit exponential response away from the two algebraic roots. -/
theorem cuspConstantLogResponse_eq_quotient {κ : ℂ}
    (hp : κ ≠ (1 / 2 : ℂ)) (hm : κ ≠ -(1 / 2 : ℂ)) (t : ℝ) :
    cuspConstantLogResponse κ t =
      (Complex.exp (-κ * (t : ℂ)) - Complex.exp (-(t : ℂ) / 2)) / ((1 / 4 : ℂ) - κ ^ 2) := by
  unfold cuspConstantLogResponse
  rw [dslope_of_ne _ hp, slope_def_module, smul_eq_mul,
    show -(1 / 2 : ℂ) * (t : ℂ) = -(t : ℂ) / 2 by ring]
  have hp2 : κ * 2 - 1 ≠ 0 := by
    intro h; apply hp; linear_combination h / 2
  have hm2 : κ * 2 + 1 ≠ 0 := by
    intro h; apply hm; linear_combination h / 2
  have hd2 : 1 - κ ^ 2 * 4 ≠ 0 := by
    intro h; apply cuspConstant_denominator_ne_zero hp hm; linear_combination h / 4
  field_simp [hp2, hm2, hd2]
  ring

/-- The removable value is an actual exponential-polynomial function. -/
@[simp] theorem cuspConstantLogResponse_half (t : ℝ) :
    cuspConstantLogResponse (1 / 2) t = (t : ℂ) * Complex.exp (-(t : ℂ) / 2) := by
  have hd : HasDerivAt (fun z : ℂ => Complex.exp (-z * (t : ℂ)))
      (-(t : ℂ) * Complex.exp (-(t : ℂ) / 2)) (1 / 2) := by
    apply (((hasDerivAt_id (1 / 2 : ℂ)).neg.mul_const (t : ℂ)).cexp).congr_deriv
    dsimp only [Pi.neg_apply, id_eq]
    rw [show -(1 / 2 : ℂ) * (t : ℂ) = -(t : ℂ) / 2 by ring]
    ring
  rw [cuspConstantLogResponse, dslope_same, hd.deriv]
  norm_num

@[simp] theorem cuspConstantLogResponse_boundary (κ : ℂ) : cuspConstantLogResponse κ 0 = 0 := by
  unfold cuspConstantLogResponse
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  by_cases hκ : κ = (1 / 2 : ℂ)
  · subst κ
    simp
  · rw [dslope_of_ne _ hκ, slope_def_module]
    simp

/-- The numerator relation includes the removable parameter without division by zero. -/
theorem cuspConstantLogResponse_numerator {κ : ℂ} (hm : κ ≠ -(1 / 2 : ℂ)) (t : ℝ) :
    ((1 / 4 : ℂ) - κ ^ 2) * cuspConstantLogResponse κ t =
      Complex.exp (-κ * (t : ℂ)) - Complex.exp (-(t : ℂ) / 2) := by
  by_cases hp : κ = (1 / 2 : ℂ)
  · subst κ
    rw [show -(1 / 2 : ℂ) * (t : ℂ) = -(t : ℂ) / 2 by ring]
    norm_num
  · rw [cuspConstantLogResponse_eq_quotient hp hm]
    exact mul_div_cancel₀ _ (cuspConstant_denominator_ne_zero hp hm)

/-- The ordinary derivative of one scalar exponential. -/
theorem hasDerivAt_cuspConstantExp (κ : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (-κ * (u : ℂ)))
      (-κ * Complex.exp (-κ * (t : ℂ))) t := by
  have h := (((hasDerivAt_id (t : ℂ)).const_mul (-κ)).cexp).comp_ofReal
  apply h.congr_deriv
  dsimp only [id_eq]
  ring

theorem hasDerivAt_cuspConstantHalfExp (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (-(u : ℂ) / 2))
      (-(1 / 2 : ℂ) * Complex.exp (-(t : ℂ) / 2)) t := by
  have h := (((hasDerivAt_id (t : ℂ)).neg.div_const 2).cexp).comp_ofReal
  apply h.congr_deriv
  dsimp only [Pi.neg_apply, id_eq]
  ring

/-- The actual profile has its ordinary first derivative at every real position. -/
theorem hasDerivAt_cuspConstantLogResponse {κ : ℂ} (hm : κ ≠ -(1 / 2 : ℂ)) (t : ℝ) :
    HasDerivAt (cuspConstantLogResponse κ)
      (Complex.exp (-κ * (t : ℂ)) / (κ + 1 / 2) -
        (1 / 2 : ℂ) * cuspConstantLogResponse κ t) t := by
  by_cases hp : κ = (1 / 2 : ℂ)
  · subst κ
    have heq : cuspConstantLogResponse (1 / 2 : ℂ) =
        (fun u : ℝ => (u : ℂ) * Complex.exp (-(u : ℂ) / 2)) :=
      funext cuspConstantLogResponse_half
    rw [heq]
    have hi : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := (hasDerivAt_id (t : ℂ)).comp_ofReal
    apply (hi.mul (hasDerivAt_cuspConstantHalfExp t)).congr_deriv
    rw [show -(1 / 2 : ℂ) * (t : ℂ) = -(t : ℂ) / 2 by ring]
    norm_num
    ring
  · have heq : cuspConstantLogResponse κ = (fun u : ℝ =>
        (Complex.exp (-κ * (u : ℂ)) - Complex.exp (-(u : ℂ) / 2)) /
          ((1 / 4 : ℂ) - κ ^ 2)) := funext (cuspConstantLogResponse_eq_quotient hp hm)
    rw [heq]
    apply (((hasDerivAt_cuspConstantExp κ t).sub (hasDerivAt_cuspConstantHalfExp t)).div_const
      ((1 / 4 : ℂ) - κ ^ 2)).congr_deriv
    have hm2 : κ * 2 + 1 ≠ 0 := by
      intro h; apply hm; linear_combination h / 2
    have hd2 : 1 - κ ^ 2 * 4 ≠ 0 := by
      intro h; apply cuspConstant_denominator_ne_zero hp hm; linear_combination h / 4
    field_simp [hm2, hd2]
    ring

/-- The scalar form combination is exactly one outgoing exponential. -/
theorem deriv_cuspConstantLogResponse_add_half {κ : ℂ} (hm : κ ≠ -(1 / 2 : ℂ)) (t : ℝ) :
    deriv (cuspConstantLogResponse κ) t + (1 / 2 : ℂ) * cuspConstantLogResponse κ t =
      Complex.exp (-κ * (t : ℂ)) / (κ + 1 / 2) := by
  rw [(hasDerivAt_cuspConstantLogResponse hm t).deriv]
  ring

/-- An actual second-derivative certificate, including the removable physical parameter. -/
theorem hasDerivAt_deriv_cuspConstantLogResponse {κ : ℂ}
    (hm : κ ≠ -(1 / 2 : ℂ)) (t : ℝ) :
    HasDerivAt (deriv (cuspConstantLogResponse κ))
      (κ ^ 2 * cuspConstantLogResponse κ t - Complex.exp (-(t : ℂ) / 2)) t := by
  have heq : deriv (cuspConstantLogResponse κ) = (fun u : ℝ =>
      Complex.exp (-κ * (u : ℂ)) / (κ + 1 / 2) - (1 / 2 : ℂ) * cuspConstantLogResponse κ u) :=
    funext fun u => (hasDerivAt_cuspConstantLogResponse hm u).deriv
  rw [heq]
  apply (((hasDerivAt_cuspConstantExp κ t).div_const (κ + 1 / 2)).sub
    ((hasDerivAt_cuspConstantLogResponse hm t).const_mul (1 / 2 : ℂ))).congr_deriv
  have hn := cuspConstantLogResponse_numerator hm t
  simp only [neg_mul, neg_div] at hn
  have hc := cuspConstant_add_half_ne_zero hm
  have hm2 : κ * 2 + 1 ≠ 0 := by
    intro h; apply hm; linear_combination h / 2
  field_simp [hm2]
  linear_combination (8 * κ + 4) * hn

/-- The profile solves the genuine transformed constant-source equation. -/
theorem cuspConstantLogResponse_forcedODE {κ : ℂ} (hm : κ ≠ -(1 / 2 : ℂ)) (t : ℝ) :
    -deriv (deriv (cuspConstantLogResponse κ)) t + κ ^ 2 * cuspConstantLogResponse κ t =
      Complex.exp (-(t : ℂ) / 2) := by
  rw [(hasDerivAt_deriv_cuspConstantLogResponse hm t).deriv]
  ring

end GapFamily.Analytic
