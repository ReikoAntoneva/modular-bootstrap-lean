import GapFamily.Analytic.Spatial.SpatialPointLaplacePower
import GapFamily.Analytic.Spatial.ComplexGammaLaplace

/-! Ordinary Gamma–Laplace factorization of the actual point kernel at every
complex parameter with positive real part. All one-sided and product integrals
are proved integrable before the point identity is assembled. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open MeasureTheory Set

/-- The ordinary one-sided Gamma density for either reflected point rate. -/
def pointGammaLaplaceFactor (s z w : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * Complex.exp (-pointLaplaceRate z w * (t : ℂ))

theorem integrableOn_pointGammaLaplaceFactor {s z w : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (pointGammaLaplaceFactor s z w) (Ioi 0) :=
  integrableOn_gammaLaplaceIntegrand hs (pointLaplaceRate_re_pos hz hw)

/-- Each actual point rate lies in the convergence half-plane of the proved
complex Gamma–Laplace integral. -/
theorem integral_pointGammaLaplaceFactor {s z w : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.im) (hw : 0 < w.im) :
    (∫ t : ℝ in Ioi 0, pointGammaLaplaceFactor s z w t) =
      Complex.Gamma s / (pointLaplaceRate z w) ^ s := by
  unfold pointGammaLaplaceFactor
  rw [integral_gammaLaplaceIntegrand hs (pointLaplaceRate_re_pos hz hw), Complex.cpow_neg]
  ring

/-- Exact factorization of the actual point kernel, with its original one-quarter
normalization and both ordinary convergent Gamma integrals. -/
theorem pointKernel_eq_double_gammaLaplace {s z w : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel s z w =
      (1 / 4 : ℂ) * (pointGammaLaplaceScale z w : ℂ) ^ s / Complex.Gamma s ^ 2 *
        (∫ t : ℝ in Ioi 0, pointGammaLaplaceFactor s z w t) *
        (∫ t : ℝ in Ioi 0, pointGammaLaplaceFactor s w z t) := by
  rw [integral_pointGammaLaplaceFactor hs hz hw, integral_pointGammaLaplaceFactor hs hw hz]
  exact pointKernel_eq_gamma_rate_product hs hz hw

/-- Ordinary product integrability permits the subsequent cone substitution. -/
theorem integrableOn_pointGammaLaplaceProduct {s z w : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (fun p : ℝ × ℝ =>
      pointGammaLaplaceFactor s z w p.1 * pointGammaLaplaceFactor s w z p.2)
      (Ioi 0 ×ˢ Ioi 0) := by
  rw [IntegrableOn, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    ← MeasureTheory.Measure.prod_restrict]
  exact (integrableOn_pointGammaLaplaceFactor hs hz hw).smul_prod
    (integrableOn_pointGammaLaplaceFactor hs hw hz)

/-- The same kernel is the ordinary two-variable Gamma integral on the positive quadrant. -/
theorem pointKernel_eq_quadrant_gammaLaplace {s z w : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel s z w =
      (1 / 4 : ℂ) * (pointGammaLaplaceScale z w : ℂ) ^ s / Complex.Gamma s ^ 2 *
        ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioi 0,
          pointGammaLaplaceFactor s z w p.1 * pointGammaLaplaceFactor s w z p.2 := by
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod_mul, ← mul_assoc]
  exact pointKernel_eq_double_gammaLaplace hs hz hw

end GapFamily.Analytic.SpatialPoint
