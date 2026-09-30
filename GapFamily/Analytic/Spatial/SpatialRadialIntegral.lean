import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory Set

private theorem spatialRadialPrimitive_continuousOn {s : ℝ} (hs : 1 < s) :
    ContinuousOn (fun r : ℝ => -(1 - r ^ 2) ^ (s - 1) / (2 * (s - 1))) (Icc 0 1) := by
  exact ((((continuous_const.sub (continuous_id.pow 2)).rpow_const
    (fun _ => Or.inr (by linarith : 0 ≤ s - 1))).neg).div_const _).continuousOn

private theorem spatialRadialPrimitive_hasDerivAt {s r : ℝ} (hs : 1 < s)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => -(1 - t ^ 2) ^ (s - 1) / (2 * (s - 1)))
      (r * (1 - r ^ 2) ^ (s - 2)) r := by
  have hbase : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hexp : s - 1 - 1 = s - 2 := by ring
  have hden : s - 1 ≠ 0 := by linarith
  convert! ((((hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).pow 2)).rpow_const
    (Or.inl hbase.ne')).neg).div_const (2 * (s - 1)) using 1
  simp only [hexp, id_eq, Pi.sub_apply, Pi.pow_apply]
  field_simp
  ring

/-- The singular radial power is genuinely Lebesgue integrable for every real s > 1. -/
theorem integrableOn_spatialRadialDensity {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun r : ℝ => r * (1 - r ^ 2) ^ (s - 2)) (Ioo 0 1) := by
  rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
  apply intervalIntegral.integrableOn_deriv_of_nonneg
    (spatialRadialPrimitive_continuousOn hs)
    (fun r hr => spatialRadialPrimitive_hasDerivAt hs hr)
  intro r hr
  exact mul_nonneg hr.1.le (Real.rpow_nonneg (by nlinarith [hr.1, hr.2]) _)

/-- Exact radial mass, including the integrable endpoint singularity for 1 < s < 2. -/
theorem integral_spatialRadialDensity {s : ℝ} (hs : 1 < s) :
    (∫ r in Ioo (0 : ℝ) 1, r * (1 - r ^ 2) ^ (s - 2)) =
      1 / (2 * (s - 1)) := by
  have hint : IntervalIntegrable (fun r : ℝ => r * (1 - r ^ 2) ^ (s - 2)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact integrableOn_spatialRadialDensity hs
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (spatialRadialPrimitive_continuousOn hs)
    (fun r hr => spatialRadialPrimitive_hasDerivAt hs hr) hint]
  simp [Real.zero_rpow (by linarith : s - 1 ≠ 0), div_eq_mul_inv, mul_inv_rev]

end GapFamily.Analytic.SpatialPoint
