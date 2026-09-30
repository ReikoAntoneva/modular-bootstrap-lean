import GapFamily.Analytic.Poincare.Fourier.PoincareFourierIntegral
import GapFamily.Analytic.Cusp.CuspPoincareDirectRemnant
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The actual identity-coset Fourier coefficient has quotient normalization one. -/

noncomputable section
namespace GapFamily.Analytic.PoincareFourier
open Set MeasureTheory
open scoped Classical

/-- Ordinary orthogonality of the literal integer phase over the width-one interval. -/
theorem integral_cuspFourierMode_zero_one (n : ℤ) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode n x) = if n = 0 then 1 else 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [cuspFourierMode]
  · rw [ite_eq_right hn]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hc : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hnC
    have hend : cuspFourierMode n 1 = cuspFourierMode n 0 := by
      simpa using cuspFourierMode_add_int n 0 1
    change (∫ x in (0 : ℝ)..1,
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * (x : ℂ))) = 0
    rw [integral_exp_mul_complex hc]
    change (cuspFourierMode n 1 - cuspFourierMode n 0) /
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) = 0
    rw [hend, sub_self, zero_div]

private theorem cuspFourierMode_neg_mul (j J : ℤ) (x : ℝ) :
    cuspFourierMode (-j) x * cuspFourierMode J x = cuspFourierMode (J - j) x := by
  unfold cuspFourierMode
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The identity cusp coset contributes one literal seed, with the output
frequency subtracted from its integer input frequency. -/
theorem fourierTerm_identity (j J : ℤ) (s : ℂ) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    fourierTerm j J s y hy identityCuspCoset x =
      (y : ℂ) ^ s * cuspFourierMode (J - j) x := by
  rw [fourierTerm, complexPoincareTerm_identity, complexPointSeed_zero_eq_cuspFourierMode]
  change cuspFourierMode (-j) x * ((y : ℂ) ^ s * cuspFourierMode J x) = _
  rw [mul_left_comm, cuspFourierMode_neg_mul]

/-- The direct identity-coset coefficient has exact diagonal normalization,
for every complex exponent and every positive height. -/
theorem integral_fourierTerm_identity (j J : ℤ) (s : ℂ) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierTerm j J s y hy identityCuspCoset x) =
      if j = J then (y : ℂ) ^ s else 0 := by
  classical
  have he : (fun x : ℝ => fourierTerm j J s y hy identityCuspCoset x) =
      fun x => (y : ℂ) ^ s * cuspFourierMode (J - j) x := by
    funext x
    exact fourierTerm_identity j J s y hy x
  rw [he, intervalIntegral.integral_const_mul, integral_cuspFourierMode_zero_one]
  by_cases hj : j = J
  · subst j
    simp
  · have hsub : J - j ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
    simp only [ite_eq_right hsub, mul_zero, ite_eq_right hj]

/-- Removing the identity coset leaves a genuinely convergent Fourier tail. -/
theorem hasSum_integral_fourierTerm_nonidentity (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    HasSum (fun q : CuspCoset => if q = identityCuspCoset then 0 else
      ∫ x in (0 : ℝ)..1, fourierTerm j J s y hy q x)
      ((∫ x in (0 : ℝ)..1, fourierSeries j J s y hy x) -
        (if j = J then (y : ℂ) ^ s else 0)) := by
  simpa only [integral_fourierTerm_identity] using
    hasSum_ite_sub_hasSum (hasSum_integral_fourierTerm j J hs y hy) identityCuspCoset

/-- The actual horizontal Fourier coefficient splits into the exact diagonal
identity term and its convergent nonidentity tail. -/
theorem integral_fourierSeries_eq_identity_add (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierSeries j J s y hy x) =
      (if j = J then (y : ℂ) ^ s else 0) +
        ∑' q : CuspCoset, if q = identityCuspCoset then 0 else
          ∫ x in (0 : ℝ)..1, fourierTerm j J s y hy q x := by
  rw [integral_fourierSeries_eq_tsum j J hs y hy,
    (hasSum_integral_fourierTerm j J hs y hy).summable.tsum_eq_add_tsum_ite identityCuspCoset,
    integral_fourierTerm_identity]

end GapFamily.Analytic.PoincareFourier
