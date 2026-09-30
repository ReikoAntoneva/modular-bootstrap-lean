import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Scalar rank-one normalization

The scalar numerator `sqrt E` against `dE / E` has thermal density
`E ^ (-1/2) * exp (-2π y E)`.  Its integral is ordinary and convergent;
after multiplication by `sqrt y` it gives the constant `1 / sqrt 2`.
-/

namespace GapFamily.Analytic

open Real Set MeasureTheory

/-- Ordinary integrability of the scalar rank-one density at every temperature. -/
theorem scalar_rank_one_integrable {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun E : ℝ => E ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * y * E))
      (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2 : ℝ))
      (b := 2 * π * y) (by norm_num) (by norm_num) (by positivity))

/-- Exact transform of the scalar rank-one density. -/
theorem scalar_rank_one_integral {y : ℝ} (hy : 0 < y) :
    (∫ E : ℝ in Ioi 0, E ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * y * E)) =
      1 / Real.sqrt (2 * y) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 1 / 2) (r := 2 * π * y) (by norm_num) (by positivity)
  norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
    neg_mul] at h
  simp only [neg_mul]
  rw [h, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity),
    Real.sqrt_one]
  rw [show 2 * π * y = (2 * y) * π by ring, Real.sqrt_mul (by positivity)]
  field_simp [Real.sqrt_ne_zero'.mpr (show 0 < 2 * y by positivity),
    Real.sqrt_ne_zero'.mpr Real.pi_pos]

/-- A rank-one density contributes a constant to the reduced partition function. -/
theorem scalar_rank_one_normalization {y : ℝ} (hy : 0 < y) :
    Real.sqrt y *
      (∫ E : ℝ in Ioi 0, E ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * y * E)) =
      1 / Real.sqrt 2 := by
  rw [scalar_rank_one_integral hy, Real.sqrt_mul (by norm_num)]
  field_simp [Real.sqrt_ne_zero'.mpr hy, Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]

/-- An origin atom contributes `sqrt y`, distinct from the rank-one density. -/
theorem scalar_origin_atom_transform (y : ℝ) :
    Real.sqrt y *
      (∫ E : ℝ, Real.exp (-2 * π * y * E) ∂Measure.dirac 0) = Real.sqrt y := by
  simp

end GapFamily.Analytic
