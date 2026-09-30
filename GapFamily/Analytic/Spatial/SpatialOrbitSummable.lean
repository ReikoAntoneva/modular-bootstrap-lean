import GapFamily.Analytic.Spatial.SpatialPointKernelComplexIntegrable
import GapFamily.Analytic.Spatial.SpatialPointKernelLocalComparison
import GapFamily.Analytic.Spatial.SpatialSummabilityTopology
import GapFamily.Analytic.Spatial.SpatialOrbitKernelBasic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology MatrixGroups

theorem norm_pointKernel_real_exponent (σ : ℝ) (z w : UpperHalfPlane) :
    ‖pointKernel (σ : ℂ) z w‖ = (1 / 4 : ℝ) * pointParameter z w ^ (-σ) := by
  simp only [pointKernel, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (pointParameter_pos z.im_pos w.im_pos),
    Complex.neg_re, Complex.ofReal_re]
  norm_num

theorem pointKernel_norm_le_eight_rpow_mul {σ : ℝ} (hσ : 0 ≤ σ)
    (z z' w : UpperHalfPlane)
    (hq : pointParameter z w ≤ 8 * pointParameter z' w) :
    ‖pointKernel (σ : ℂ) z' w‖ ≤ (8 : ℝ) ^ σ * ‖pointKernel (σ : ℂ) z w‖ := by
  have hqdiv : pointParameter z w / 8 ≤ pointParameter z' w := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    nlinarith
  have hpow := Real.rpow_le_rpow_of_nonpos
    (div_pos (pointParameter_pos z.im_pos w.im_pos) (by norm_num)) hqdiv (neg_nonpos.mpr hσ)
  rw [Real.div_rpow (pointParameter_pos z.im_pos w.im_pos).le (by norm_num),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8) σ, div_inv_eq_mul] at hpow
  rw [norm_pointKernel_real_exponent, norm_pointKernel_real_exponent]
  calc
    _ ≤ (1 / 4 : ℝ) * (pointParameter z w ^ (-σ) * (8 : ℝ) ^ σ) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = _ := by ring

theorem pointKernel_norm_local_comparison {σ : ℝ} (hσ : 0 ≤ σ)
    (z z' w : UpperHalfPlane) (hd : ‖(z' : ℂ) - (z : ℂ)‖ ≤ z.im / 2) :
    ‖pointKernel (σ : ℂ) z' w‖ ≤ (8 : ℝ) ^ σ * ‖pointKernel (σ : ℂ) z w‖ ∧
      ‖pointKernel (σ : ℂ) z w‖ ≤ (8 : ℝ) ^ σ * ‖pointKernel (σ : ℂ) z' w‖ := by
  have hq := pointParameter_local_comparison z.im_pos z'.im_pos w.im_pos hd
  exact ⟨pointKernel_norm_le_eight_rpow_mul hσ z z' w hq.2,
    pointKernel_norm_le_eight_rpow_mul hσ z' z w hq.1⟩

theorem summable_norm_pointKernel_orbit_iff_of_near {σ : ℝ} (hσ : 0 ≤ σ)
    (z z' w : UpperHalfPlane) (hd : ‖(z' : ℂ) - (z : ℂ)‖ ≤ z.im / 2) :
    Summable (fun γ : SL(2, ℤ) => ‖pointKernel (σ : ℂ) z' (γ • w : UpperHalfPlane)‖) ↔
      Summable (fun γ : SL(2, ℤ) => ‖pointKernel (σ : ℂ) z (γ • w : UpperHalfPlane)‖) := by
  constructor
  · intro hz'
    exact Summable.of_nonneg_of_le (fun γ => norm_nonneg _)
      (fun γ => (pointKernel_norm_local_comparison hσ z z' (γ • w) hd).2)
      (hz'.mul_left ((8 : ℝ) ^ σ))
  · intro hz
    exact Summable.of_nonneg_of_le (fun γ => norm_nonneg _)
      (fun γ => (pointKernel_norm_local_comparison hσ z z' (γ • w) hd).1)
      (hz.mul_left ((8 : ℝ) ^ σ))

theorem eventually_summable_norm_pointKernel_orbit_iff {σ : ℝ} (hσ : 0 ≤ σ)
    (z w : UpperHalfPlane) :
    ∀ᶠ z' : UpperHalfPlane in 𝓝 z,
      Summable (fun γ : SL(2, ℤ) => ‖pointKernel (σ : ℂ) z' (γ • w : UpperHalfPlane)‖) ↔
        Summable (fun γ : SL(2, ℤ) => ‖pointKernel (σ : ℂ) z (γ • w : UpperHalfPlane)‖) := by
  have hnear : {z' : UpperHalfPlane | ‖(z' : ℂ) - (z : ℂ)‖ < z.im / 2} ∈ 𝓝 z := by
    apply (isOpen_lt (UpperHalfPlane.continuous_coe.sub continuous_const).norm
      continuous_const).mem_nhds
    change ‖(z : ℂ) - (z : ℂ)‖ < z.im / 2
    simpa only [sub_self, norm_zero] using half_pos z.im_pos
  filter_upwards [hnear] with z' hz'
  exact summable_norm_pointKernel_orbit_iff_of_near hσ z z' w hz'.le

/-- The actual almost-everywhere orbit sum propagates to every upper point. -/
theorem summable_norm_spatialOrbit_real (σ : ℝ) (hσ : 1 < σ)
    (z w : UpperHalfPlane) :
    Summable (fun γ : SL(2, ℤ) => ‖pointKernel (σ : ℂ) z (γ • w : UpperHalfPlane)‖) := by
  apply forall_of_eventually_iff_of_ae_modularMeasure
    (fun z : UpperHalfPlane =>
      Summable (fun γ : SL(2, ℤ) => ‖pointKernel (σ : ℂ) z (γ • w : UpperHalfPlane)‖))
    (fun z => eventually_summable_norm_pointKernel_orbit_iff (by linarith : 0 ≤ σ) z w)
    (ae_summable_norm_spatialOrbit_right (σ : ℂ) (by simpa using hσ) w) z

/-- Every literal complex orbit series is absolutely convergent throughout Re(s)>1. -/
theorem summable_norm_spatialOrbit (s : ℂ) (hs : 1 < s.re) (z w : UpperHalfPlane) :
    Summable (fun γ : SL(2, ℤ) => ‖pointKernel s z (γ • w : UpperHalfPlane)‖) := by
  exact (summable_norm_spatialOrbit_real s.re hs z w).congr
    (fun γ => (norm_pointKernel_eq_realPart s z (γ • w)).symm)

theorem summable_spatialOrbit (s : ℂ) (hs : 1 < s.re) (z w : UpperHalfPlane) :
    Summable (fun γ : SL(2, ℤ) => pointKernel s z (γ • w : UpperHalfPlane)) :=
  (summable_norm_spatialOrbit s hs z w).of_norm

end GapFamily.Analytic.SpatialPoint
