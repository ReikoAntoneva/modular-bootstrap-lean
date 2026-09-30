import GapFamily.Analytic.Poincare.PoincareAnalytic
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationAction
import GapFamily.Analytic.Cusp.CuspPoincareDirectRemnant

/-!
Exact matrix identities for the convergent Poincare Fourier calculation.
No regrouping, integration, or continuation is asserted here.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareFourier
open Complex Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-- The literal nonparabolic modular action separates its rational cusp value. -/
theorem smul_eq_div_sub_inv (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (hc : γ 1 0 ≠ 0) :
    (↑(γ • τ : UpperHalfPlane) : ℂ) =
      (γ 0 0 : ℂ) / (γ 1 0 : ℂ) -
        1 / ((γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) := by
  have hc' : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hd : (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) ≠ 0 :=
    rawModularAction_denom_ne_zero γ τ.im_pos
  have hd' : (τ : ℂ) * (γ 1 0 : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by
    simpa only [mul_comm] using hd
  have hdet : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) -
      (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  rw [← rawModularAction_coe, rawModularAction_apply]
  field_simp [hc', hd, hd']
  linear_combination -hdet

/-- The real coordinate retains the same exact rational phase correction. -/
theorem re_smul_eq_div_sub_inv_re (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (hc : γ 1 0 ≠ 0) :
    (γ • τ : UpperHalfPlane).re =
      (γ 0 0 : ℝ) / (γ 1 0 : ℝ) -
        (1 / ((γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)))).re := by
  have h := congrArg Complex.re (smul_eq_div_sub_inv γ τ hc)
  have hdiv : (γ 0 0 : ℂ) / (γ 1 0 : ℂ) =
      (((γ 0 0 : ℝ) / (γ 1 0 : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hdiv] at h
  simpa only [UpperHalfPlane.coe_re, Complex.sub_re, Complex.ofReal_re] using h

/-- The actual zero-energy seed separates the arithmetic cusp phase and the
remaining inverse-denominator phase without any exponent restriction. -/
theorem complexPointSeed_zero_smul_eq_height_phase (J : ℤ) (s : ℂ)
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (hc : γ 1 0 ≠ 0) :
    complexPointSeed 0 J s (γ • τ) =
      ((τ.im / Complex.normSq ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) : ℝ) : ℂ) ^ s *
        cuspFourierMode J ((γ 0 0 : ℝ) / (γ 1 0 : ℝ)) *
        cuspFourierMode J
          (-(1 / ((γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)))).re) := by
  rw [complexPointSeed_zero_eq_cuspFourierMode,
    ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply,
    re_smul_eq_div_sub_inv_re γ τ hc]
  simp only [cuspFourierMode, Complex.ofReal_sub, Complex.ofReal_neg]
  rw [mul_sub, Complex.exp_sub]
  simp only [Complex.exp_neg, div_eq_mul_inv, mul_neg]
  ring

end GapFamily.Analytic.PoincareFourier
