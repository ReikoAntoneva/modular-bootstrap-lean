import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

theorem cuspHalfLineLaplace_exp_norm_sq (β : ℂ) (t : ℝ) :
    ‖Complex.exp (-β * (t : ℂ))‖ ^ 2 = Real.exp ((-2 * β.re) * t) := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, mul_zero, sub_zero, Nat.cast_ofNat]
  ring

theorem cuspHalfLineLaplace_exp_norm_sq_integrable {β : ℂ} (hβ : 0 < β.re) :
    IntegrableOn (fun t : ℝ => ‖Complex.exp (-β * (t : ℂ))‖ ^ 2) (Ioi 0) := by
  simp only [cuspHalfLineLaplace_exp_norm_sq]
  exact integrableOn_exp_mul_Ioi (a := -2 * β.re) (by linarith) 0

theorem cuspHalfLineLaplace_exp_memLp {β : ℂ} (hβ : 0 < β.re) :
    MemLp (fun t : ℝ => Complex.exp (-β * (t : ℂ))) 2
      (volume.restrict (Ioi 0)) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp (-β * (t : ℂ))))).aestronglyMeasurable).mpr
  exact cuspHalfLineLaplace_exp_norm_sq_integrable hβ

theorem cuspHalfLineLaplace_exp_norm_sq_integral {β : ℂ} (hβ : 0 < β.re) :
    (∫ t : ℝ in Ioi 0, ‖Complex.exp (-β * (t : ℂ))‖ ^ 2) = (2 * β.re)⁻¹ := by
  simp_rw [cuspHalfLineLaplace_exp_norm_sq]
  rw [integral_exp_mul_Ioi (a := -2 * β.re) (by linarith) 0]
  simp [neg_mul, div_eq_mul_inv]

end GapFamily.Analytic
