import GapFamily.Analytic.Spatial.SpatialPointLaplace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Point spatial Fourier–Laplace cone

The real-frequency Fourier–Laplace representation at `s = 1/2` follows from the
ordinary Gamma integral on the positive quadrant by `E = u + v`, `J = u - v`.
The determinant and square-root density give the exact coefficient one.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open MeasureTheory Set
open scoped Matrix

/-- Positive energy lies above the real-frequency light cone. -/
def pointLaplaceCone : Set (ℝ × ℝ) := {p | |p.2| < p.1}

/-- The positive-quadrant to light-cone linear coordinate map. -/
def pointConeMap : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) !![1, 1; 1, -1]

theorem pointConeMap_apply (p : ℝ × ℝ) : pointConeMap p = (p.1 + p.2, p.1 - p.2) := by
  simp [pointConeMap, Matrix.toLin_finTwoProd_apply, sub_eq_add_neg]

theorem pointConeMap_det : pointConeMap.det = -2 := by
  rw [pointConeMap, LinearMap.det_toLin]
  norm_num [Matrix.det_fin_two]

theorem pointConeMap_injective : Function.Injective pointConeMap := by
  intro p q h
  rw [pointConeMap_apply, pointConeMap_apply] at h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  ext <;> dsimp at h₁ h₂ ⊢ <;> linarith

theorem pointConeMap_image_quadrant :
    pointConeMap '' (Ioi 0 ×ˢ Ioi 0) = pointLaplaceCone := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change |(pointConeMap q).2| < (pointConeMap q).1
    rw [pointConeMap_apply]
    rcases hq with ⟨hu, hv⟩
    change 0 < q.1 at hu
    change 0 < q.2 at hv
    exact abs_lt.mpr ⟨by dsimp; linarith, by dsimp; linarith⟩
  · intro hp
    change |p.2| < p.1 at hp
    have hp' := abs_lt.mp hp
    refine ⟨((p.1 + p.2) / 2, (p.1 - p.2) / 2), ?_, ?_⟩
    · constructor <;> change (0 : ℝ) < _ <;> linarith [hp'.1, hp'.2]
    · rw [pointConeMap_apply]
      ext <;> dsimp <;> ring

/-- The actual threshold Fourier–Laplace density at continuous real frequency. -/
def pointConeDensity (z w : ℂ) (p : ℝ × ℝ) : ℂ :=
  ((p.1 ^ 2 - p.2 ^ 2) ^ (-(1 / 2) : ℝ) : ℝ) *
    Complex.exp (-2 * Real.pi *
      (((z.im + w.im) * p.1 : ℝ) + Complex.I * ((z.re - w.re) * p.2 : ℝ)))

theorem pointThresholdLaplaceProduct_eq_cone (z w : ℂ) {p : ℝ × ℝ}
    (hp : p ∈ Ioi 0 ×ˢ Ioi 0) :
    pointThresholdLaplaceFactor z w p.1 * pointThresholdLaplaceFactor w z p.2 =
      (2 : ℝ) • pointConeDensity z w (pointConeMap p) := by
  rcases hp with ⟨hu, hv⟩
  change 0 < p.1 at hu
  change 0 < p.2 at hv
  have hD : (p.1 + p.2) ^ 2 - (p.1 - p.2) ^ 2 = 4 * p.1 * p.2 := by ring
  have hfour : (4 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have hweight : ((p.1 + p.2) ^ 2 - (p.1 - p.2) ^ 2) ^ (-(1 / 2) : ℝ) =
      1 / 2 * p.1 ^ (-(1 / 2) : ℝ) * p.2 ^ (-(1 / 2) : ℝ) := by
    rw [hD, Real.mul_rpow (by positivity) hv.le,
      Real.mul_rpow (by norm_num) hu.le, hfour]
  rw [pointConeMap_apply]
  simp only [pointThresholdLaplaceFactor, pointConeDensity, hweight,
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  have he : -pointLaplaceRate z w * (p.1 : ℂ) + -pointLaplaceRate w z * (p.2 : ℂ) =
      -2 * Real.pi * (((z.im + w.im) * (p.1 + p.2) : ℝ) +
        Complex.I * ((z.re - w.re) * (p.1 - p.2) : ℝ)) := by
    simp only [pointLaplaceRate, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub]
    ring
  calc
    _ = ((p.1 ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) *
        ((p.2 ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) *
        (Complex.exp (-pointLaplaceRate z w * p.1) *
          Complex.exp (-pointLaplaceRate w z * p.2)) := by ring
    _ = _ := by
      rw [← Complex.exp_add, he]
      push_cast
      ring

theorem integrableOn_pointConeDensity {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (pointConeDensity z w) pointLaplaceCone := by
  rw [← pointConeMap_image_quadrant]
  apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (measurableSet_Ioi.prod measurableSet_Ioi)
    (fun p hp => pointConeMap.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)
    pointConeMap_injective.injOn (pointConeDensity z w)).mpr
  apply (integrableOn_pointThresholdLaplaceProduct hz hw).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  convert pointThresholdLaplaceProduct_eq_cone z w hp using 1
  change |pointConeMap.det| • _ = (2 : ℝ) • _
  norm_num [pointConeMap_det]

theorem integral_pointConeDensity_eq_quadrant (z w : ℂ) :
    (∫ p : ℝ × ℝ in pointLaplaceCone, pointConeDensity z w p) =
      ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioi 0,
        pointThresholdLaplaceFactor z w p.1 * pointThresholdLaplaceFactor w z p.2 := by
  rw [← pointConeMap_image_quadrant]
  rw [integral_image_eq_integral_abs_det_fderiv_smul (f := pointConeMap) volume
    (measurableSet_Ioi.prod measurableSet_Ioi)
    (fun p hp => pointConeMap.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)
    pointConeMap_injective.injOn (pointConeDensity z w)]
  apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi)
  intro p hp
  change |pointConeMap.det| • _ = _
  norm_num only [pointConeMap_det, abs_neg, abs_two]
  exact (pointThresholdLaplaceProduct_eq_cone z w hp).symm

/-- The actual threshold point spatial kernel equals its ordinary real-frequency cone integral.
The coefficient is exactly `C_(1/2) = 1`; convergence is proved separately above. -/
theorem pointKernel_one_half_eq_cone_laplace {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel (1 / 2) z w = (Real.sqrt (z.im * w.im) : ℂ) *
      ∫ p : ℝ × ℝ in pointLaplaceCone, pointConeDensity z w p := by
  rw [integral_pointConeDensity_eq_quadrant]
  exact pointKernel_one_half_eq_quadrant_laplace hz hw

theorem measurableSet_pointLaplaceCone : MeasurableSet pointLaplaceCone :=
  (isOpen_lt continuous_snd.abs continuous_fst).measurableSet

private theorem integral_cone_indicator_section (z w : ℂ) (J : ℝ) :
    (∫ E : ℝ, pointLaplaceCone.indicator (pointConeDensity z w) (E, J)) =
      ∫ E : ℝ in Ioi |J|, pointConeDensity z w (E, J) := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun E => by
    simp only [Set.indicator_apply, pointLaplaceCone, mem_ofPred_eq, mem_Ioi]

theorem integrable_pointConeDensity_frequency {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    Integrable (fun J : ℝ => ∫ E : ℝ in Ioi |J|, pointConeDensity z w (E, J)) := by
  have h := (integrable_indicator_iff measurableSet_pointLaplaceCone).mpr
    (integrableOn_pointConeDensity hz hw)
  change Integrable _ (volume.prod volume) at h
  simpa only [integral_cone_indicator_section] using h.integral_prod_right

/-- An ordinary Fubini identity with continuous real frequency outside the energy integral. -/
theorem pointKernel_one_half_eq_frequency_laplace {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel (1 / 2) z w = (Real.sqrt (z.im * w.im) : ℂ) *
      ∫ J : ℝ, ∫ E : ℝ in Ioi |J|, pointConeDensity z w (E, J) := by
  rw [pointKernel_one_half_eq_cone_laplace hz hw,
    ← integral_indicator measurableSet_pointLaplaceCone]
  congr 1
  have h := (integrable_indicator_iff measurableSet_pointLaplaceCone).mpr
    (integrableOn_pointConeDensity hz hw)
  change Integrable _ (volume.prod volume) at h
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    integral_prod_symm _ h]
  simp only [integral_cone_indicator_section]

end GapFamily.Analytic.SpatialPoint
