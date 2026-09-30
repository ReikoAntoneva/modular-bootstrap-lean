import GapFamily.Analytic.Spatial.SpatialPointLaplaceCone

/-! The general complex-parameter cone density under the actual linear
positive-quadrant change of variables. All power products have positive
real bases, so no complex logarithm branch is crossed.
-/

noncomputable section

namespace GapFamily.Analytic.SpatialPoint

open Set MeasureTheory

/-- The ordinary full cone density at one complex parameter. -/
def pointGammaConeDensity (s z w : ℂ) (p : ℝ × ℝ) : ℂ :=
  ((p.1 ^ 2 - p.2 ^ 2 : ℝ) : ℂ) ^ (s - 1) *
    Complex.exp (-2 * Real.pi *
      (((z.im + w.im) * p.1 : ℝ) + Complex.I * ((z.re - w.re) * p.2 : ℝ)))

/-- Positive cone coordinates separate the actual complex power and both
exponential factors, with the exact factor `4^(s-1)`. -/
theorem pointGammaConeDensity_map (s z w : ℂ) {p : ℝ × ℝ}
    (hp : p ∈ Ioi 0 ×ˢ Ioi 0) :
    pointGammaConeDensity s z w (pointConeMap p) =
      (4 : ℂ) ^ (s - 1) *
        ((p.1 : ℂ) ^ (s - 1) * Complex.exp (-pointLaplaceRate z w * (p.1 : ℂ))) *
        ((p.2 : ℂ) ^ (s - 1) * Complex.exp (-pointLaplaceRate w z * (p.2 : ℂ))) := by
  rcases hp with ⟨hu, hv⟩
  change 0 < p.1 at hu
  change 0 < p.2 at hv
  have hD : (p.1 + p.2) ^ 2 - (p.1 - p.2) ^ 2 = 4 * p.1 * p.2 := by ring
  have hweight : (((p.1 + p.2) ^ 2 - (p.1 - p.2) ^ 2 : ℝ) : ℂ) ^ (s - 1) =
      (4 : ℂ) ^ (s - 1) * (p.1 : ℂ) ^ (s - 1) * (p.2 : ℂ) ^ (s - 1) := by
    rw [hD, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) hv.le,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) hu.le]
    norm_num
  have he : -pointLaplaceRate z w * (p.1 : ℂ) + -pointLaplaceRate w z * (p.2 : ℂ) =
      -2 * Real.pi * (((z.im + w.im) * (p.1 + p.2) : ℝ) +
        Complex.I * ((z.re - w.re) * (p.1 - p.2) : ℝ)) := by
    simp only [pointLaplaceRate, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub]
    ring
  rw [pointConeMap_apply, pointGammaConeDensity, hweight, ← he, Complex.exp_add]
  ring

/-- The determinant of the actual coordinate map contributes the factor two. -/
theorem integral_pointGammaConeDensity_eq_quadrant (s z w : ℂ) :
    (∫ p : ℝ × ℝ in pointLaplaceCone, pointGammaConeDensity s z w p) =
      ((2 : ℂ) * (4 : ℂ) ^ (s - 1)) *
        ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioi 0,
          ((p.1 : ℂ) ^ (s - 1) * Complex.exp (-pointLaplaceRate z w * (p.1 : ℂ))) *
          ((p.2 : ℂ) ^ (s - 1) * Complex.exp (-pointLaplaceRate w z * (p.2 : ℂ))) := by
  rw [← pointConeMap_image_quadrant]
  rw [integral_image_eq_integral_abs_det_fderiv_smul (f := pointConeMap) volume
    (measurableSet_Ioi.prod measurableSet_Ioi)
    (fun p hp => pointConeMap.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)
    pointConeMap_injective.injOn (pointGammaConeDensity s z w)]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi)
  intro p hp
  change |pointConeMap.det| • _ = _
  rw [pointGammaConeDensity_map s z w hp]
  norm_num only [pointConeMap_det, abs_neg, abs_two, Complex.real_smul, Complex.ofReal_ofNat]
  ring

/-- The ordinary cone integral is the product of the two ordinary Gamma
integrals with its complete Jacobian and power normalization. -/
theorem integral_pointGammaConeDensity_eq_product (s z w : ℂ) :
    (∫ p : ℝ × ℝ in pointLaplaceCone, pointGammaConeDensity s z w p) =
      ((2 : ℂ) * (4 : ℂ) ^ (s - 1)) *
        (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-pointLaplaceRate z w * t)) *
        (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-pointLaplaceRate w z * t)) := by
  rw [integral_pointGammaConeDensity_eq_quadrant,
    show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod_mul
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-pointLaplaceRate z w * t))
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-pointLaplaceRate w z * t))
      (Ioi 0) (Ioi 0)]
  ring

end GapFamily.Analytic.SpatialPoint
