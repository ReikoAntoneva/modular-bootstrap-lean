import GapFamily.Analytic.Spatial.SpatialOrbitFirstBound
import GapFamily.Analytic.Spatial.SpatialOrbitOperator
import GapFamily.Analytic.Spatial.SpatialSummabilityTopology

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology MatrixGroups

/-- The actual positive real orbit kernel has two-sided comparison on an upper ball. -/
theorem spatialOrbitKernel_norm_local_comparison (s : ℝ) (hs : 1 < s)
    (z z' w : UpperHalfPlane) (hd : ‖(z' : ℂ) - (z : ℂ)‖ ≤ z.im / 2) :
    ‖spatialOrbitKernel (s : ℂ) z' w‖ ≤ (8 : ℝ)^s * ‖spatialOrbitKernel (s : ℂ) z w‖ ∧
      ‖spatialOrbitKernel (s : ℂ) z w‖ ≤ (8 : ℝ)^s * ‖spatialOrbitKernel (s : ℂ) z' w‖ := by
  rw [norm_spatialOrbitKernel_eq_half_tsum_norm s hs z' w,
    norm_spatialOrbitKernel_eq_half_tsum_norm s hs z w]
  have hz := summable_norm_spatialOrbit_real s hs z w
  have hz' := summable_norm_spatialOrbit_real s hs z' w
  have h1 := hz'.tsum_le_tsum
    (fun γ => (pointKernel_norm_local_comparison (by linarith : 0 ≤ s) z z' (γ • w) hd).1)
    (hz.mul_left ((8 : ℝ)^s))
  have h2 := hz.tsum_le_tsum
    (fun γ => (pointKernel_norm_local_comparison (by linarith : 0 ≤ s) z z' (γ • w) hd).2)
    (hz'.mul_left ((8 : ℝ)^s))
  simp only [tsum_mul_left] at h1 h2
  constructor <;> nlinarith

/-- Literal row integrability is equivalent at nearby spatial points. -/
theorem integrable_spatialOrbitKernel_mul_iff_of_near (s : ℝ) (hs : 1 < s)
    (F : ModularHilbert) (z z' : UpperHalfPlane)
    (hd : ‖(z' : ℂ) - (z : ℂ)‖ ≤ z.im / 2) :
    Integrable (fun w : UpperHalfPlane => spatialOrbitKernel (s : ℂ) z' w * F w) modularMeasure ↔
      Integrable (fun w : UpperHalfPlane => spatialOrbitKernel (s : ℂ) z w * F w) modularMeasure := by
  have hm (v : UpperHalfPlane) : AEStronglyMeasurable
      (fun w : UpperHalfPlane => spatialOrbitKernel (s : ℂ) v w * F w) modularMeasure :=
    (((continuous_spatialOrbitKernel (s : ℂ) (by simpa using hs)).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul (Lp.memLp F).aestronglyMeasurable
  constructor
  · intro hi
    apply (hi.norm.const_mul ((8 : ℝ)^s)).mono' (hm z)
    filter_upwards [] with w
    simp only [norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (spatialOrbitKernel_norm_local_comparison s hs z z' w hd).2 (norm_nonneg (F w))).trans_eq
        (mul_assoc _ _ _)
  · intro hi
    apply (hi.norm.const_mul ((8 : ℝ)^s)).mono' (hm z')
    filter_upwards [] with w
    simp only [norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (spatialOrbitKernel_norm_local_comparison s hs z z' w hd).1 (norm_nonneg (F w))).trans_eq
        (mul_assoc _ _ _)

/-- Row integrability is locally constant in the first upper-half-plane point. -/
theorem eventually_integrable_spatialOrbitKernel_mul_iff (s : ℝ) (hs : 1 < s)
    (F : ModularHilbert) (z : UpperHalfPlane) :
    ∀ᶠ z' : UpperHalfPlane in 𝓝 z,
      Integrable (fun w : UpperHalfPlane => spatialOrbitKernel (s : ℂ) z' w * F w) modularMeasure ↔
        Integrable (fun w : UpperHalfPlane => spatialOrbitKernel (s : ℂ) z w * F w) modularMeasure := by
  have hnear : {z' : UpperHalfPlane | ‖(z' : ℂ) - (z : ℂ)‖ < z.im / 2} ∈ 𝓝 z := by
    apply (isOpen_lt (UpperHalfPlane.continuous_coe.sub continuous_const).norm
      continuous_const).mem_nhds
    change ‖(z : ℂ) - (z : ℂ)‖ < z.im / 2
    simpa only [sub_self, norm_zero] using half_pos z.im_pos
  filter_upwards [hnear] with z' hz'
  exact integrable_spatialOrbitKernel_mul_iff_of_near s hs F z z' hz'.le

/-- Every actual modular L² input has an integrable literal kernel product in every row. -/
theorem integrable_spatialOrbitKernel_mul (s : ℝ) (hs : 1 < s)
    (F : ModularHilbert) (z : UpperHalfPlane) :
    Integrable (fun w : UpperHalfPlane => spatialOrbitKernel (s : ℂ) z w * F w) modularMeasure := by
  exact forall_of_eventually_iff_of_ae_modularMeasure
    (fun z => Integrable (fun w : UpperHalfPlane => spatialOrbitKernel (s : ℂ) z w * F w) modularMeasure)
    (eventually_integrable_spatialOrbitKernel_mul_iff s hs F)
    (spatialOrbitIntegralOperator_integrable_ae s hs F) z

end GapFamily.Analytic.SpatialPoint
