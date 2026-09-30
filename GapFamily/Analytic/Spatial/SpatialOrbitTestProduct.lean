import GapFamily.Analytic.Spatial.SpatialOrbitRowIntegrable
import GapFamily.Analytic.Spatial.SpatialOrbitProductMeasurable
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual mixed-measure integrability of compact tests against arbitrary modular L² inputs. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

/-- The literal row norm integral is continuous at every upper-half-plane point.
The majorant is the integrable row at that point times the proved local factor. -/
theorem continuous_integral_norm_spatialOrbitKernel_mul (s : ℝ) (hs : 1 < s)
    (F : ModularHilbert) :
    Continuous (fun z : UpperHalfPlane =>
      ∫ w : UpperHalfPlane, ‖spatialOrbitKernel (s : ℂ) z w * F w‖ ∂modularMeasure) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hnear : {z' : UpperHalfPlane | ‖(z' : ℂ) - (z : ℂ)‖ < z.im / 2} ∈ 𝓝 z := by
    apply (isOpen_lt (UpperHalfPlane.continuous_coe.sub continuous_const).norm
      continuous_const).mem_nhds
    change ‖(z : ℂ) - (z : ℂ)‖ < z.im / 2
    simpa only [sub_self, norm_zero] using half_pos z.im_pos
  apply continuousAt_of_dominated
    (bound := fun w : UpperHalfPlane =>
      (8 : ℝ) ^ s * ‖spatialOrbitKernel (s : ℂ) z w * F w‖)
  · exact Eventually.of_forall (fun z' =>
      (integrable_spatialOrbitKernel_mul s hs F z').norm.aestronglyMeasurable)
  · filter_upwards [hnear] with z' hz'
    apply Eventually.of_forall
    intro w
    simp only [norm_norm, norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (spatialOrbitKernel_norm_local_comparison s hs z z' w hz'.le).1 (norm_nonneg (F w))).trans_eq
        (mul_assoc _ _ _)
  · exact (integrable_spatialOrbitKernel_mul s hs F z).norm.const_mul ((8 : ℝ) ^ s)
  · apply Eventually.of_forall
    intro w
    exact (((continuous_spatialOrbitKernel (s : ℂ) (by simpa using hs)).comp
      (continuous_id.prodMk continuous_const)).mul continuous_const).norm.continuousAt

/-- Compact multiplication makes the outer integral of the actual row norm finite. -/
theorem integrable_integral_norm_spatialOrbitKernel_test (s : ℝ) (hs : 1 < s)
    (F : ModularHilbert) (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) :
    Integrable (fun z : UpperHalfPlane => ∫ w : UpperHalfPlane,
      ‖a z * (spatialOrbitKernel (s : ℂ) z w * F w)‖ ∂modularMeasure) volume := by
  have hi : Integrable (fun z : UpperHalfPlane => ‖a z‖ *
      (∫ w : UpperHalfPlane, ‖spatialOrbitKernel (s : ℂ) z w * F w‖ ∂modularMeasure)) volume :=
    (ha.norm.mul (continuous_integral_norm_spatialOrbitKernel_mul s hs F)).integrable_of_hasCompactSupport
      hc.norm.mul_right
  simpa only [norm_mul, integral_const_mul] using hi

/-- The full compact-test kernel product is ordinarily integrable on the mixed
whole-half-plane by modular-region product measure, for every actual L² input. -/
theorem integrable_spatialOrbitKernel_test_product (s : ℝ) (hs : 1 < s)
    (F : ModularHilbert) (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) :
    Integrable (fun p : UpperHalfPlane × UpperHalfPlane =>
      a p.1 * (spatialOrbitKernel (s : ℂ) p.1 p.2 * F p.2))
      ((volume : Measure UpperHalfPlane).prod modularMeasure) := by
  apply (integrable_prod_iff (aestronglyMeasurable_spatialOrbit_test_product s hs F a ha)).mpr
  exact ⟨Eventually.of_forall (fun z =>
    (integrable_spatialOrbitKernel_mul s hs F z).const_mul (a z)),
    integrable_integral_norm_spatialOrbitKernel_test s hs F a ha hc⟩

end GapFamily.Analytic.SpatialPoint
