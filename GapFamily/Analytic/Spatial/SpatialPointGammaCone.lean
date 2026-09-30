import GapFamily.Analytic.Spatial.SpatialPointGammaConeDensity
import GapFamily.Analytic.Spatial.SpatialPointGammaConeConstant
import GapFamily.Analytic.Spatial.SpatialPointGammaLaplace

/-! The actual complex-parameter point kernel is an ordinary, absolutely
convergent cone integral. The positive-quadrant substitution and Fubini give
the real-frequency representation throughout `0 < re s`.
-/

noncomputable section

namespace GapFamily.Analytic.SpatialPoint

open Set MeasureTheory

theorem integrableOn_pointGammaConeDensity {s z w : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (pointGammaConeDensity s z w) pointLaplaceCone := by
  rw [← pointConeMap_image_quadrant]
  apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (measurableSet_Ioi.prod measurableSet_Ioi)
    (fun p hp => pointConeMap.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)
    pointConeMap_injective.injOn (pointGammaConeDensity s z w)).mpr
  apply ((integrableOn_pointGammaLaplaceProduct hs hz hw).const_mul
    ((2 : ℂ) * (4 : ℂ) ^ (s - 1))).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  change _ = |pointConeMap.det| • pointGammaConeDensity s z w (pointConeMap p)
  rw [pointGammaConeDensity_map s z w hp]
  simp only [pointGammaLaplaceFactor, pointConeMap_det, abs_neg, abs_two,
    Complex.real_smul, Complex.ofReal_ofNat]
  ring

/-- Exact cone representation of the actual point kernel, with the prescribed
complex Gamma normalization and ordinary absolute convergence. -/
theorem pointKernel_eq_cone_gammaLaplace {s z w : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel s z w = spatialLaplaceConstantComplex s *
      ((z.im * w.im : ℝ) : ℂ) ^ s *
        ∫ p : ℝ × ℝ in pointLaplaceCone, pointGammaConeDensity s z w p := by
  rw [pointKernel_eq_double_gammaLaplace hs hz hw,
    integral_pointGammaConeDensity_eq_product]
  have hscale : pointGammaLaplaceScale z w = 16 * Real.pi ^ 2 * (z.im * w.im) := by
    unfold pointGammaLaplaceScale
    ring
  rw [hscale, pointGammaConeConstant_eq s (z.im * w.im) (mul_pos hz hw)]
  unfold pointGammaLaplaceFactor
  ring

theorem integral_pointGammaCone_indicator_section (s z w : ℂ) (J : ℝ) :
    (∫ E : ℝ, pointLaplaceCone.indicator (pointGammaConeDensity s z w) (E, J)) =
      ∫ E : ℝ in Ioi |J|, pointGammaConeDensity s z w (E, J) := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun E => by
    simp only [Set.indicator_apply, pointLaplaceCone, mem_ofPred_eq, mem_Ioi]

theorem integrable_pointGammaConeDensity_frequency {s z w : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.im) (hw : 0 < w.im) :
    Integrable (fun J : ℝ => ∫ E : ℝ in Ioi |J|, pointGammaConeDensity s z w (E, J)) := by
  have h := (integrable_indicator_iff measurableSet_pointLaplaceCone).mpr
    (integrableOn_pointGammaConeDensity hs hz hw)
  change Integrable _ (volume.prod volume) at h
  simpa only [integral_pointGammaCone_indicator_section] using h.integral_prod_right

theorem integral_pointGammaConeDensity_eq_frequency {s z w : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.im) (hw : 0 < w.im) :
    (∫ p : ℝ × ℝ in pointLaplaceCone, pointGammaConeDensity s z w p) =
      ∫ J : ℝ, ∫ E : ℝ in Ioi |J|, pointGammaConeDensity s z w (E, J) := by
  rw [← integral_indicator measurableSet_pointLaplaceCone]
  have h := (integrable_indicator_iff measurableSet_pointLaplaceCone).mpr
    (integrableOn_pointGammaConeDensity hs hz hw)
  change Integrable _ (volume.prod volume) at h
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    integral_prod_symm _ h]
  simp only [integral_pointGammaCone_indicator_section]

/-- The ordinary real-frequency Fourier--Laplace representation of the actual
point kernel. Joint absolute integrability for `0 < re s` justifies Fubini;
the inner integral is absolutely convergent for almost every frequency. -/
theorem pointKernel_eq_frequency_gammaLaplace {s z w : ℂ}
    (hs : 0 < s.re) (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel s z w = spatialLaplaceConstantComplex s *
      ((z.im * w.im : ℝ) : ℂ) ^ s *
        ∫ J : ℝ, ∫ E : ℝ in Ioi |J|, pointGammaConeDensity s z w (E, J) := by
  rw [pointKernel_eq_cone_gammaLaplace hs hz hw,
    integral_pointGammaConeDensity_eq_frequency hs hz hw]

end GapFamily.Analytic.SpatialPoint
