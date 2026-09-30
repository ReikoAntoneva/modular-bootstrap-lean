import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
namespace GapFamily.Analytic.BesselCoshOrder
open Set MeasureTheory

/-- A Gaussian majorant, uniform in the positive spatial parameter and bounded complex order. -/
def majorant (a R u : ℝ) : ℝ :=
  Real.exp (R ^ 2 / a) * Real.exp (-(a / 4) * u ^ 2)

theorem majorant_pos (a R u : ℝ) : 0 < majorant a R u := by
  unfold majorant
  positivity

/-- The proposed bound is genuinely integrable, even on the whole real line. -/
theorem majorant_integrable_global {a R : ℝ} (ha : 0 < a) :
    Integrable (majorant a R) :=
  (integrable_exp_neg_mul_sq (div_pos ha (by norm_num : (0 : ℝ) < 4))).const_mul _

theorem majorant_integrable {a R : ℝ} (ha : 0 < a) :
    IntegrableOn (majorant a R) (Ioi 0) :=
  (majorant_integrable_global ha).integrableOn

/-- The actual nonnegative cosh power series contains its quadratic term. -/
theorem sq_half_le_cosh {u : ℝ} (hu : 0 ≤ u) : u ^ 2 / 2 ≤ Real.cosh u := by
  have h := sum_le_hasSum ({1} : Finset ℕ)
    (fun n _ => div_nonneg (pow_nonneg hu _) (Nat.cast_nonneg _)) (Real.hasSum_cosh u)
  norm_num at h
  exact h

/-- The two exponential summands give a uniform norm bound for complex cosh. -/
theorem norm_cosh_mul_le_exp {κ : ℂ} {R u : ℝ} (hκ : ‖κ‖ ≤ R) (hu : 0 ≤ u) :
    ‖Complex.cosh (κ * (u : ℂ))‖ ≤ Real.exp (R * u) := by
  have hn : ‖κ * (u : ℂ)‖ ≤ R * u := by
    rw [norm_mul, Complex.norm_of_nonneg hu]
    exact mul_le_mul_of_nonneg_right hκ hu
  have hp := Complex.norm_exp_le_exp_norm (κ * (u : ℂ))
  have hm := Complex.norm_exp_le_exp_norm (-(κ * (u : ℂ)))
  simp only [norm_neg] at hm
  have he := Real.exp_le_exp.mpr hn
  have hsum := norm_add_le
    (Complex.exp (κ * (u : ℂ))) (Complex.exp (-(κ * (u : ℂ))))
  rw [Complex.cosh, norm_div, Complex.norm_two]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  linarith

/-- Completion of the square makes the remaining exponent explicitly Gaussian. -/
theorem quadratic_exponent_bound {a R u : ℝ} (ha : 0 < a) :
    -(a / 2) * u ^ 2 + R * u ≤ R ^ 2 / a - (a / 4) * u ^ 2 := by
  refine le_of_mul_le_mul_left (a := a) ?_ ha
  have hd : a * (R ^ 2 / a) = R ^ 2 := by field_simp [ha.ne']
  nlinarith [sq_nonneg (a * u - 2 * R)]

/-- The literal cosh integral kernel is dominated uniformly for t≥a>0 and bounded complex order. -/
theorem norm_integrand_le_majorant {a t R u : ℝ} {κ : ℂ}
    (ha : 0 < a) (hat : a ≤ t) (hκ : ‖κ‖ ≤ R) (hu : 0 ≤ u) :
    ‖Complex.exp (-(t : ℂ) * (Real.cosh u : ℂ)) * Complex.cosh (κ * (u : ℂ))‖ ≤
      majorant a R u := by
  have hexp : ‖Complex.exp (-(t : ℂ) * (Real.cosh u : ℂ))‖ =
      Real.exp (-t * Real.cosh u) := by simp [Complex.norm_exp]
  have hquad : a * (u ^ 2 / 2) ≤ t * Real.cosh u :=
    (mul_le_mul_of_nonneg_left (sq_half_le_cosh hu) ha.le).trans
      (mul_le_mul_of_nonneg_right hat (Real.cosh_pos u).le)
  calc
    _ ≤ Real.exp (-t * Real.cosh u) * Real.exp (R * u) := by
      rw [norm_mul, hexp]
      exact mul_le_mul_of_nonneg_left (norm_cosh_mul_le_exp hκ hu) (Real.exp_pos _).le
    _ = Real.exp (-t * Real.cosh u + R * u) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (R ^ 2 / a - (a / 4) * u ^ 2) := by
      apply Real.exp_le_exp.mpr
      exact (show -t * Real.cosh u + R * u ≤ -(a / 2) * u ^ 2 + R * u by
        nlinarith).trans (quadratic_exponent_bound ha)
    _ = majorant a R u := by
      unfold majorant
      rw [← Real.exp_add]
      congr 1
      ring

end GapFamily.Analytic.BesselCoshOrder
