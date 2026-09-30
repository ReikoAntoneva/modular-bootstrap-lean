import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import GapFamily.Analytic.Spatial.SpatialRadialIntegral

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open Set Filter MeasureTheory MeasureTheory.Measure Metric
open scoped Topology

def spatialDiskDensity (s : ℝ) (ζ : ℂ) : ℝ := (1 - ‖ζ‖ ^ 2) ^ (s - 2)

theorem integral_unitDisk_radial (f : ℝ → ℝ) :
    (∫ ζ : ℂ in ball 0 1, f ‖ζ‖) =
      2 * Real.pi * ∫ r : ℝ in Ioo 0 1, r * f r := by
  calc
    (∫ ζ : ℂ in ball 0 1, f ‖ζ‖) =
        ∫ ζ : ℂ, (ball 0 1).indicator (fun z : ℂ => f ‖z‖) ζ :=
      (integral_indicator measurableSet_ball).symm
    _ = ∫ p in polarCoord.target,
        p.1 • (ball 0 1).indicator (fun z : ℂ => f ‖z‖) (Complex.polarCoord.symm p) :=
      (Complex.integral_comp_polarCoord_symm _).symm
    _ = ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
        ((Iio 1).indicator (fun r : ℝ => r * f r) p.1) * 1 := by
      rw [polarCoord_target]
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      rintro ⟨r, θ⟩ ⟨hr, hθ⟩
      have hr0 : 0 < r := hr
      by_cases hr1 : r < 1 <;>
        simp [Set.indicator, Metric.mem_ball, abs_of_pos hr0, hr1]
    _ = (∫ r : ℝ in Ioi 0, (Iio 1).indicator (fun r : ℝ => r * f r) r) *
        ∫ _ : ℝ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [← setIntegral_prod_mul, volume_eq_prod]
    _ = (∫ r : ℝ in Ioo 0 1, r * f r) * (2 * Real.pi) := by
      rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
      congr 1
      simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_real_Ioo_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]),
        sub_neg_eq_add, smul_eq_mul, mul_one]
      ring
    _ = _ := by ring

theorem integrableOn_spatialDiskDensity {s : ℝ} (hs : 1 < s) :
    IntegrableOn (spatialDiskDensity s) (ball (0 : ℂ) 1) := by
  change IntegrableOn (fun ζ : ℂ => (fun r : ℝ => (1 - r ^ 2) ^ (s - 2)) ‖ζ‖)
    (ball (0 : ℂ) 1)
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun r : ℝ => (1 - r ^ 2) ^ (s - 2))]
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul] using
    integrableOn_spatialRadialDensity hs

theorem integral_spatialDiskDensity {s : ℝ} (hs : 1 < s) :
    (∫ ζ : ℂ in ball 0 1, spatialDiskDensity s ζ) = Real.pi / (s - 1) := by
  change (∫ ζ : ℂ in ball 0 1, (fun r : ℝ => (1 - r ^ 2) ^ (s - 2)) ‖ζ‖) = _
  rw [integral_unitDisk_radial (fun r : ℝ => (1 - r ^ 2) ^ (s - 2)),
    integral_spatialRadialDensity hs]
  field_simp

theorem integrableOn_spatialDiskDensity_complex {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun ζ : ℂ => (spatialDiskDensity s ζ : ℂ)) (ball (0 : ℂ) 1) :=
  (integrableOn_spatialDiskDensity hs).ofReal

theorem integral_spatialDiskDensity_complex {s : ℝ} (hs : 1 < s) :
    (∫ ζ : ℂ in ball 0 1, (spatialDiskDensity s ζ : ℂ)) =
      (Real.pi / (s - 1) : ℝ) := by
  rw [integral_complex_ofReal, integral_spatialDiskDensity hs]

end GapFamily.Analytic.SpatialPoint
