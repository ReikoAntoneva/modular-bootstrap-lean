import BTZEntropy.Coefficient
import BTZEntropy.Analytic.GaussianMomentRecurrence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.Basic

/-!
# Gaussian realization of the coefficient functional

The finite Gaussian functional used in the coefficient algorithm is related
to integration on the imaginary saddle direction.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BTZEntropy

@[simp] theorem imaginaryGaussianMoment_one (h : ℝ) :
    imaginaryGaussianMoment h 1 = 0 := by
  simp [imaginaryGaussianMoment]

theorem imaginaryGaussianMoment_add_two {h : ℝ} (hh : h ≠ 0) (n : ℕ) :
    imaginaryGaussianMoment h (n + 2) =
      -((n + 1 : ℕ) : ℝ) / h * imaginaryGaussianMoment h n := by
  by_cases hn : Even n
  · have hn2 : Even (n + 2) := hn.add (by decide)
    have hnval : n = 2 * (n / 2) := by
      have hmod := Nat.even_iff.mp hn
      omega
    have hcast : (n : ℝ) = 2 * (n / 2 : ℕ) := by exact_mod_cast hnval
    simp only [imaginaryGaussianMoment, hn2, hn, ↓reduceIte]
    rw [show (n + 2) / 2 = n / 2 + 1 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hf : ((n / 2).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  · have hn2 : ¬Even (n + 2) := fun he => hn ((Nat.even_add.mp he).mpr (by decide))
    simp [imaginaryGaussianMoment, hn, hn2]

/-- The actual unnormalized Gaussian moment on the imaginary displacement line. -/
def imaginaryGaussianIntegral (h : ℝ) (n : ℕ) : ℂ :=
  ∫ t : ℝ, ((t : ℂ) * Complex.I) ^ n * (Real.exp (-h * t ^ 2 / 2) : ℂ)

theorem imaginaryGaussianIntegral_eq_real (h : ℝ) (n : ℕ) :
    imaginaryGaussianIntegral h n =
      Complex.I ^ n * ((∫ t : ℝ, t ^ n * Real.exp (-h * t ^ 2 / 2) : ℝ) : ℂ) := by
  unfold imaginaryGaussianIntegral
  calc
    (∫ t : ℝ, ((t : ℂ) * Complex.I) ^ n * (Real.exp (-h * t ^ 2 / 2) : ℂ)) =
        ∫ t : ℝ, Complex.I ^ n * ((t ^ n * Real.exp (-h * t ^ 2 / 2) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with t
      push_cast
      ring
    _ = _ := by rw [integral_const_mul, integral_complex_ofReal]

theorem integrable_imaginaryGaussian {h : ℝ} (hh : 0 < h) (n : ℕ) :
    Integrable (fun t : ℝ =>
      ((t : ℂ) * Complex.I) ^ n * (Real.exp (-h * t ^ 2 / 2) : ℂ)) := by
  have hr := (integrable_gaussianRawMoment hh n).ofReal (𝕜 := ℂ)
  refine (hr.const_mul (Complex.I ^ n)).congr ?_
  filter_upwards [] with t
  change Complex.I ^ n * ((t ^ n * Real.exp (-h * t ^ 2 / 2) : ℝ) : ℂ) = _
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  ring

theorem integrable_polynomial_gaussian {h : ℝ} (hh : 0 < h) (p : Polynomial ℝ) :
    Integrable (fun t : ℝ =>
      p.eval₂ Complex.ofRealHom ((t : ℂ) * Complex.I) *
        (Real.exp (-h * t ^ 2 / 2) : ℂ)) := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply integrable_finsetSum
  intro n hn
  simpa only [mul_assoc, Complex.ofRealHom_eq_coe] using
    (integrable_imaginaryGaussian hh n).const_mul (p.coeff n : ℂ)

/-- Finite polynomial integration reduces to the actual Gaussian moments. -/
theorem integral_polynomial_gaussian_eq_sum {h : ℝ} (hh : 0 < h) (p : Polynomial ℝ) :
    (∫ t : ℝ, p.eval₂ Complex.ofRealHom ((t : ℂ) * Complex.I) *
        (Real.exp (-h * t ^ 2 / 2) : ℂ)) =
      p.sum (fun n a => (a : ℂ) * imaginaryGaussianIntegral h n) := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [imaginaryGaussianIntegral, mul_assoc, integral_const_mul]
    rfl
  · intro n hn
    simpa only [mul_assoc, Complex.ofRealHom_eq_coe] using
      (integrable_imaginaryGaussian hh n).const_mul (p.coeff n : ℂ)

/-- Every coefficient moment is the corresponding genuine Gaussian integral. -/
theorem imaginaryGaussianIntegral_eq_moment {h : ℝ} (hh : 0 < h) (n : ℕ) :
    imaginaryGaussianIntegral h n =
      (Real.sqrt (2 * Real.pi / h) : ℂ) * (imaginaryGaussianMoment h n : ℂ) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [imaginaryGaussianIntegral_eq_real]
      change Complex.I ^ 0 * (gaussianRawMoment h 0 : ℂ) = _
      simp [gaussianRawMoment_zero]
  | one =>
      rw [imaginaryGaussianIntegral_eq_real]
      change Complex.I ^ 1 * (gaussianRawMoment h 1 : ℂ) = _
      simp [gaussianRawMoment_one]
  | more n ih _ =>
      rw [imaginaryGaussianIntegral_eq_real] at ih ⊢
      change Complex.I ^ (n + 2) * (gaussianRawMoment h (n + 2) : ℂ) = _
      change Complex.I ^ n * (gaussianRawMoment h n : ℂ) = _ at ih
      rw [gaussianRawMoment_add_two hh, imaginaryGaussianMoment_add_two (ne_of_gt hh),
        pow_add, Complex.I_sq]
      push_cast
      calc
        Complex.I ^ n * -1 * (((n : ℂ) + 1) / (h : ℂ) * (gaussianRawMoment h n : ℂ)) =
            (-((n : ℂ) + 1) / (h : ℂ)) * (Complex.I ^ n * (gaussianRawMoment h n : ℂ)) := by
              ring
        _ = _ := by rw [ih]; ring

/-- The finite polynomial functional is exactly Gaussian integration, with its
normalizing determinant displayed explicitly. -/
theorem integral_polynomial_gaussian_eq_evaluation {h : ℝ} (hh : 0 < h)
    (p : Polynomial ℝ) :
    (∫ t : ℝ, p.eval₂ Complex.ofRealHom ((t : ℂ) * Complex.I) *
        (Real.exp (-h * t ^ 2 / 2) : ℂ)) =
      (Real.sqrt (2 * Real.pi / h) : ℂ) * (gaussianEvaluation h p : ℂ) := by
  rw [integral_polynomial_gaussian_eq_sum hh]
  simp only [gaussianEvaluation, Polynomial.sum, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [imaginaryGaussianIntegral_eq_moment hh]
  ring

theorem normalized_integral_polynomial_gaussian {h : ℝ} (hh : 0 < h)
    (p : Polynomial ℝ) :
    (∫ t : ℝ, p.eval₂ Complex.ofRealHom ((t : ℂ) * Complex.I) *
        (Real.exp (-h * t ^ 2 / 2) : ℂ)) / (Real.sqrt (2 * Real.pi / h) : ℂ) =
      (gaussianEvaluation h p : ℂ) := by
  rw [integral_polynomial_gaussian_eq_evaluation hh]
  apply mul_div_cancel_left₀
  exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi / h))

end BTZEntropy
