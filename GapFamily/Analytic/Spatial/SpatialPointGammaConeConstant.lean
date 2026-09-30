import GapFamily.Analytic.Spatial.SpatialPointFourierLaplaceBasic

/-! Exact complex-power normalization for the positive-quadrant to cone
change of variables. All powered real bases are positive, and the Gamma
denominator is retained throughout, including its totalized zero values.
-/

noncomputable section

namespace GapFamily.Analytic.SpatialPoint

/-- The product Gamma prefactor equals the prescribed cone normalization
times the positive-quadrant Jacobian and power factor. -/
theorem pointGammaConeConstant_eq (s : ℂ) (yv : ℝ) (hyv : 0 < yv) :
    (1 / 4 : ℂ) * ((16 * Real.pi ^ 2 * yv : ℝ) : ℂ) ^ s /
        Complex.Gamma s ^ 2 =
      spatialLaplaceConstantComplex s * (yv : ℂ) ^ s *
        ((2 : ℂ) * (4 : ℂ) ^ (s - 1)) := by
  have hproduct (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      ((a * b : ℝ) : ℂ) ^ s = (a : ℂ) ^ s * (b : ℂ) ^ s := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha hb]
  have hfour : (4 : ℂ) ^ s = (2 : ℂ) ^ s * (2 : ℂ) ^ s := by
    have h := Complex.natCast_mul_natCast_cpow 2 2 s
    norm_num at h
    exact h
  have hsixteen : (16 : ℂ) ^ s = (4 : ℂ) ^ s * (4 : ℂ) ^ s := by
    have h := Complex.natCast_mul_natCast_cpow 4 4 s
    norm_num at h
    exact h
  have hpi : ((Real.pi ^ 2 : ℝ) : ℂ) ^ s = (Real.pi : ℂ) ^ (2 * s) := by
    rw [Complex.ofReal_pow, pow_two,
      Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le Real.pi_pos.le,
      show 2 * s = s + s by ring,
      Complex.cpow_add s s (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
  have htwo : (2 : ℂ) ^ (2 * s) = (2 : ℂ) ^ s * (2 : ℂ) ^ s := by
    rw [show 2 * s = s + s by ring, Complex.cpow_add s s (by norm_num)]
  rw [hproduct (16 * Real.pi ^ 2) yv (by positivity) hyv.le,
    hproduct 16 (Real.pi ^ 2) (by norm_num) (sq_nonneg _), hpi]
  simp only [Complex.ofReal_ofNat, spatialLaplaceConstantComplex,
    Complex.cpow_sub (2 * s) 1 (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_sub s 1 (by norm_num : (4 : ℂ) ≠ 0),
    Complex.cpow_one, hsixteen, hfour, htwo]
  ring

end GapFamily.Analytic.SpatialPoint
