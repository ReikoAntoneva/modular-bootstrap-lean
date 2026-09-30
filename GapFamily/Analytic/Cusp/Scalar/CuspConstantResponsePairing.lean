import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseBasic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory Set
/-!
# Actual constant-source pairing in logarithmic cusp coordinate

The response against the transformed constant is an ordinary absolutely convergent
integral on `Re κ > -1/2`, including the removable value `κ = 1/2`.
-/

noncomputable section
namespace GapFamily.Analytic
private theorem response_pairing_eq (κ : ℂ) (t : ℝ) :
    Complex.exp (-(t : ℂ) / 2) *
        ((Complex.exp (-κ * t) - Complex.exp (-(t : ℂ) / 2)) / (1 / 4 - κ ^ 2)) =
      (Complex.exp (-(κ + 1 / 2) * t) - Complex.exp (-(t : ℂ))) /
        (1 / 4 - κ ^ 2) := by
  rw [← mul_div_assoc, mul_sub, ← Complex.exp_add, ← Complex.exp_add]
  congr 2 <;> congr 1 <;> ring

private theorem response_pairing_away_integrable {κ : ℂ}
    (hκ : -(1 / 2 : ℝ) < κ.re) :
    IntegrableOn (fun t : ℝ =>
      (Complex.exp (-(κ + 1 / 2) * t) - Complex.exp (-(t : ℂ))) /
        (1 / 4 - κ ^ 2)) (Ioi 0) := by
  have hk : (-(κ + 1 / 2)).re < 0 := by simp; linarith
  have hi := integrableOn_exp_mul_complex_Ioi hk (0 : ℝ)
  have hj : IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ))) (Ioi 0) := by
    simpa using integrableOn_exp_mul_complex_Ioi (a := (-1 : ℂ)) (by norm_num) (0 : ℝ)
  exact (hi.sub hj).div_const _

private theorem response_pairing_away_integral {κ : ℂ}
    (hκ : -(1 / 2 : ℝ) < κ.re) (hne : κ ≠ 1 / 2) :
    (∫ t : ℝ in Ioi 0,
      (Complex.exp (-(κ + 1 / 2) * t) - Complex.exp (-(t : ℂ))) /
        (1 / 4 - κ ^ 2)) = 1 / (κ + 1 / 2) ^ 2 := by
  have hk : (-(κ + 1 / 2)).re < 0 := by simp; linarith
  have hi := integrableOn_exp_mul_complex_Ioi hk (0 : ℝ)
  have hj : IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ))) (Ioi 0) := by
    simpa using integrableOn_exp_mul_complex_Ioi (a := (-1 : ℂ)) (by norm_num) (0 : ℝ)
  have hjv : (∫ t : ℝ in Ioi 0, Complex.exp (-(t : ℂ))) = 1 := by
    simpa using integral_exp_mul_complex_Ioi (a := (-1 : ℂ)) (by norm_num) (0 : ℝ)
  have hp : κ + 1 / 2 ≠ 0 := by
    intro hz
    have := congrArg Complex.re hz
    simp at this
    linarith
  have hm : κ - 1 / 2 ≠ 0 := sub_ne_zero.mpr hne
  have hd : (1 / 4 : ℂ) - κ ^ 2 ≠ 0 := by
    intro hz
    have hprod : (κ + 1 / 2) * (κ - 1 / 2) = 0 := by
      linear_combination -hz
    exact (mul_ne_zero hp hm) hprod
  rw [integral_div, integral_sub hi hj, integral_exp_mul_complex_Ioi hk, hjv]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  simp only [neg_div_neg_eq]
  have hp' : κ * 2 + 1 ≠ 0 := by
    intro hz
    apply hp
    linear_combination hz / 2
  have hd' : 1 - κ ^ 2 * 4 ≠ 0 := by
    intro hz
    apply hd
    linear_combination hz / 4
  field_simp [hp', hd']
  ring

private theorem response_pairing_half_integrable :
    IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-(t : ℂ))) (Ioi 0) := by
  have h := Complex.GammaIntegral_convergent (s := (2 : ℂ)) (by norm_num)
  simpa only [show (2 : ℂ) - 1 = 1 by norm_num, Complex.cpow_one,
    Complex.ofReal_exp, Complex.ofReal_neg, mul_comm] using h

private theorem response_pairing_half_integral :
    (∫ t : ℝ in Ioi 0, (t : ℂ) * Complex.exp (-(t : ℂ))) = 1 := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := (2 : ℂ)) (r := 1)
    (by norm_num) (by norm_num)
  simpa [show (2 : ℂ) - 1 = 1 by norm_num] using h

private theorem response_pairing_half_eq (t : ℝ) :
    Complex.exp (-(t : ℂ) / 2) * cuspConstantLogResponse (1 / 2) t =
      (t : ℂ) * Complex.exp (-(t : ℂ)) := by
  rw [cuspConstantLogResponse_half]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/-- The actual pairing with the transformed constant is ordinarily integrable
on its full convergence half-plane, including the removable parameter. -/
theorem cuspConstantLogResponse_pairing_integrable {κ : ℂ}
    (hκ : -(1 / 2 : ℝ) < κ.re) :
    IntegrableOn (fun t : ℝ =>
      Complex.exp (-(t : ℂ) / 2) * cuspConstantLogResponse κ t) (Ioi 0) := by
  by_cases he : κ = 1 / 2
  · subst κ
    simpa only [response_pairing_half_eq] using response_pairing_half_integrable
  have hm : κ ≠ -(1 / 2 : ℂ) := by
    intro hz
    subst κ
    norm_num at hκ
  simpa only [cuspConstantLogResponse_eq_quotient he hm, response_pairing_eq] using
    response_pairing_away_integrable hκ

/-- Evaluation of the ordinary pairing integral. Outside this open half-plane,
the same rational expression is only a candidate for meromorphic continuation. -/
theorem cuspConstantLogResponse_pairing {κ : ℂ}
    (hκ : -(1 / 2 : ℝ) < κ.re) :
    (∫ t : ℝ in Ioi 0,
      Complex.exp (-(t : ℂ) / 2) * cuspConstantLogResponse κ t) =
        1 / (κ + 1 / 2) ^ 2 := by
  by_cases he : κ = 1 / 2
  · subst κ
    simp only [response_pairing_half_eq]
    norm_num [response_pairing_half_integral]
  have hm : κ ≠ -(1 / 2 : ℂ) := by
    intro hz
    subst κ
    norm_num at hκ
  simpa only [cuspConstantLogResponse_eq_quotient he hm, response_pairing_eq] using
    response_pairing_away_integral hκ he

private theorem response_exp_memLp (κ : ℂ) (hκ : 0 < κ.re) :
    MemLp (fun t : ℝ => Complex.exp (-κ * (t : ℂ))) 2 (volume.restrict (Ioi 0)) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-κ * (t : ℂ)))).aestronglyMeasurable)).mpr
  have h := integrableOn_exp_mul_Ioi (a := -2 * κ.re) (by linarith) 0
  apply h.congr
  filter_upwards with t
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, mul_zero, sub_zero, Nat.cast_ofNat]
  ring

private theorem response_half_memLp : MemLp (fun t : ℝ => (t : ℂ) * Complex.exp (-(t : ℂ) / 2)) 2
    (volume.restrict (Ioi 0)) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((by fun_prop : Continuous (fun t : ℝ =>
      (t : ℂ) * Complex.exp (-(t : ℂ) / 2))).aestronglyMeasurable)).mpr
  have h := Real.GammaIntegral_convergent (s := 3) (by norm_num)
  have h' : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (2 : ℕ)) (Ioi 0) := by
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two] using h
  apply h'.congr
  filter_upwards with t
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Complex.norm_exp, ← Real.exp_nat_mul]
  have he : (2 : ℝ) * (-(t : ℂ) / 2).re = -t := by
    simp
    ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  exact mul_comm _ _


/-- The genuine scalar response lies in ordinary half-line L² on the physical branch. -/
theorem cuspConstantLogResponse_memLp {κ : ℂ} (hκ : 0 < κ.re) :
    MemLp (cuspConstantLogResponse κ) 2 (volume.restrict (Ioi 0)) := by
  by_cases hp : κ = 1 / 2
  · subst κ
    have heq : cuspConstantLogResponse (1 / 2) =
        (fun t : ℝ => (t : ℂ) * Complex.exp (-(t : ℂ) / 2)) :=
      funext cuspConstantLogResponse_half
    rw [heq]
    exact response_half_memLp
  have hm : κ ≠ -(1 / 2 : ℂ) := by
    intro hz
    subst κ
    norm_num at hκ
  have hh : MemLp (fun t : ℝ => Complex.exp (-(t : ℂ) / 2)) 2
      (volume.restrict (Ioi 0)) := by
    convert response_exp_memLp (1 / 2) (by norm_num) using 1
    ext t
    congr 1
    ring
  have heq : cuspConstantLogResponse κ = (fun t : ℝ =>
      (Complex.exp (-κ * (t : ℂ)) - Complex.exp (-(t : ℂ) / 2)) /
        (1 / 4 - κ ^ 2)) := funext (cuspConstantLogResponse_eq_quotient hp hm)
  rw [heq]
  simpa only [div_eq_mul_inv, Pi.sub_apply] using
    ((response_exp_memLp κ hκ).sub hh).mul_const ((1 / 4 - κ ^ 2)⁻¹)

/-- Its actual first derivative is also in ordinary half-line L². -/
theorem cuspConstantLogResponse_deriv_memLp {κ : ℂ} (hκ : 0 < κ.re) :
    MemLp (deriv (cuspConstantLogResponse κ)) 2 (volume.restrict (Ioi 0)) := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by
    intro hz
    subst κ
    norm_num at hκ
  have heq : deriv (cuspConstantLogResponse κ) = (fun t : ℝ =>
      Complex.exp (-κ * (t : ℂ)) / (κ + 1 / 2) -
        (1 / 2 : ℂ) * cuspConstantLogResponse κ t) :=
    funext fun t => (hasDerivAt_cuspConstantLogResponse hm t).deriv
  rw [heq]
  convert ((response_exp_memLp κ hκ).mul_const ((κ + 1 / 2)⁻¹)).sub
      ((cuspConstantLogResponse_memLp hκ).const_mul (1 / 2 : ℂ)) using 1
  ext t
  simp only [Pi.sub_apply, div_eq_mul_inv]

/-- Its actual second derivative is also in ordinary half-line L². -/
theorem cuspConstantLogResponse_deriv_deriv_memLp {κ : ℂ} (hκ : 0 < κ.re) :
    MemLp (deriv (deriv (cuspConstantLogResponse κ))) 2 (volume.restrict (Ioi 0)) := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by
    intro hz
    subst κ
    norm_num at hκ
  have hh : MemLp (fun t : ℝ => Complex.exp (-(t : ℂ) / 2)) 2
      (volume.restrict (Ioi 0)) := by
    convert response_exp_memLp (1 / 2) (by norm_num) using 1
    ext t
    congr 1
    ring
  have heq : deriv (deriv (cuspConstantLogResponse κ)) = (fun t : ℝ =>
      κ ^ 2 * cuspConstantLogResponse κ t - Complex.exp (-(t : ℂ) / 2)) :=
    funext fun t => (hasDerivAt_deriv_cuspConstantLogResponse hm t).deriv
  rw [heq]
  exact ((cuspConstantLogResponse_memLp hκ).const_mul (κ ^ 2)).sub hh

/-- The removable response has ordinary scalar mass squared two. -/
theorem cuspConstantLogResponse_half_mass :
    (∫ t : ℝ in Ioi 0, ‖cuspConstantLogResponse (1 / 2) t‖ ^ 2) = 2 := by
  simp only [cuspConstantLogResponse_half]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1)
    (by norm_num) (by norm_num)
  have h' : (∫ t : ℝ in Ioi 0, t ^ (2 : ℕ) * Real.exp (-t)) = 2 := by
    simpa [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two] using h
  rw [← h']
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Complex.norm_exp, ← Real.exp_nat_mul]
  congr 2
  simp
  ring

end GapFamily.Analytic
