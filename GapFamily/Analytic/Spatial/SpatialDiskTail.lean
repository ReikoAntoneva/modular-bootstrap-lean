import GapFamily.Analytic.Spatial.SpatialDiskIntegral

noncomputable section

namespace GapFamily.Analytic.SpatialPoint

open Set Filter MeasureTheory Metric
open scoped Topology

private theorem spatialRadialTailPrimitive_hasDerivAt {s r : ℝ} (hs : 1 < s)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun t : ℝ => -(1 - t ^ 2) ^ (s - 1) / (2 * (s - 1)))
      (r * (1 - r ^ 2) ^ (s - 2)) r := by
  have hbase : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hexp : s - 1 - 1 = s - 2 := by ring
  have hden : s - 1 ≠ 0 := by linarith
  convert! ((((hasDerivAt_const r (1 : ℝ)).sub
      ((hasDerivAt_id r).pow 2)).rpow_const
    (Or.inl hbase.ne')).neg).div_const (2 * (s - 1)) using 1
  simp only [hexp, id_eq, Pi.sub_apply, Pi.pow_apply]
  field_simp
  ring

theorem integral_spatialRadialDensity_tail {s r : ℝ} (hs : 1 < s)
    (hr : 0 < r) (hr1 : r < 1) :
    (∫ t in Ioo r 1, t * (1 - t ^ 2) ^ (s - 2)) =
      (1 - r ^ 2) ^ (s - 1) / (2 * (s - 1)) := by
  have hint : IntervalIntegrable
      (fun t : ℝ => t * (1 - t ^ 2) ^ (s - 2)) volume r 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr1.le,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (integrableOn_spatialRadialDensity hs).mono_set
      (fun t ht => ⟨hr.trans ht.1, ht.2⟩)
  have hcont : ContinuousOn
      (fun t : ℝ => -(1 - t ^ 2) ^ (s - 1) / (2 * (s - 1)))
      (Icc r 1) := by
    exact ((((continuous_const.sub (continuous_id.pow 2)).rpow_const
      (fun _ => Or.inr (by linarith : 0 ≤ s - 1))).neg).div_const _).continuousOn
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hr1.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr1.le hcont
      (fun t ht => spatialRadialTailPrimitive_hasDerivAt hs
        ⟨hr.trans ht.1, ht.2⟩) hint]
  simp [Real.zero_rpow (by linarith : s - 1 ≠ 0), neg_div]

theorem integrableOn_spatialDiskDensity_annulus {s : ℝ} (hs : 1 < s) (r : ℝ) :
    IntegrableOn (spatialDiskDensity s)
      (ball (0 : ℂ) 1 \ ball 0 r) :=
  (integrableOn_spatialDiskDensity hs).mono_set sdiff_subset

theorem integral_spatialDiskDensity_annulus {s r : ℝ} (hs : 1 < s)
    (hr : 0 < r) (hr1 : r < 1) :
    (∫ ζ : ℂ in ball 0 1 \ ball 0 r, spatialDiskDensity s ζ) =
      Real.pi / (s - 1) * (1 - r ^ 2) ^ (s - 1) := by
  have hset : ball (0 : ℂ) 1 \ ball 0 r =
      ball 0 1 ∩ {ζ : ℂ | r ≤ ‖ζ‖} := by
    ext ζ
    simp [Metric.mem_ball, not_lt]
  have hmeas : MeasurableSet {ζ : ℂ | r ≤ ‖ζ‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hrad : Ioo (0 : ℝ) 1 ∩ Ici r = Ico r 1 := by
    ext t
    constructor
    · intro ht
      exact ⟨ht.2, ht.1.2⟩
    · intro ht
      exact ⟨⟨hr.trans_le ht.1, ht.2⟩, ht.1⟩
  rw [hset, ← setIntegral_indicator hmeas]
  calc
    (∫ ζ : ℂ in ball 0 1,
        {ζ : ℂ | r ≤ ‖ζ‖}.indicator (spatialDiskDensity s) ζ) =
        ∫ ζ : ℂ in ball 0 1,
          ((Ici r).indicator (fun t : ℝ => (1 - t ^ 2) ^ (s - 2))) ‖ζ‖ := by
      congr 1
    _ = 2 * Real.pi * ∫ t : ℝ in Ioo 0 1,
        t * (Ici r).indicator (fun t : ℝ => (1 - t ^ 2) ^ (s - 2)) t :=
      integral_unitDisk_radial _
    _ = 2 * Real.pi * ∫ t : ℝ in Ioo 0 1,
        (Ici r).indicator (fun t : ℝ => t * (1 - t ^ 2) ^ (s - 2)) t := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ Ici r <;> simp [Set.indicator, ht]
    _ = 2 * Real.pi * ∫ t : ℝ in Ioo r 1,
        t * (1 - t ^ 2) ^ (s - 2) := by
      rw [setIntegral_indicator measurableSet_Ici, hrad, integral_Ico_eq_integral_Ioo]
    _ = _ := by
      rw [integral_spatialRadialDensity_tail hs hr hr1]
      have hs1 : s - 1 ≠ 0 := by linarith
      field_simp

theorem integrableOn_normalizedSpatialDiskDensity_annulus {s : ℝ}
    (hs : 1 < s) (r : ℝ) :
    IntegrableOn (fun ζ : ℂ => ((s - 1) / Real.pi) * spatialDiskDensity s ζ)
      (ball (0 : ℂ) 1 \ ball 0 r) :=
  (integrableOn_spatialDiskDensity_annulus hs r).const_mul _

theorem integral_normalizedSpatialDiskDensity_annulus {s r : ℝ} (hs : 1 < s)
    (hr : 0 < r) (hr1 : r < 1) :
    (∫ ζ : ℂ in ball 0 1 \ ball 0 r,
      ((s - 1) / Real.pi) * spatialDiskDensity s ζ) =
        (1 - r ^ 2) ^ (s - 1) := by
  rw [integral_const_mul, integral_spatialDiskDensity_annulus hs hr hr1]
  have hs1 : s - 1 ≠ 0 := by linarith
  field_simp

end GapFamily.Analytic.SpatialPoint
