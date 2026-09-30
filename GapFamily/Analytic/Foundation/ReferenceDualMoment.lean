import GapFamily.Analytic.Foundation.ReferenceMeasure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Dual moments of the physical reference measure

The weak kernel bound is a sum of an energy square-root product and a spin
product. Weighted Cauchy–Schwarz with the fourth-power energy weight therefore
requires the two ordinary integrals proved here. The scalar energy numerator
cancels the singular reference density exactly; the scalar spin numerator is zero.
-/

noncomputable section

open Real Set MeasureTheory

namespace GapFamily.Analytic

/-- Decay of order strictly greater than one is integrable on the positive half-line. -/
theorem integrableOn_one_div_one_add_pow {n : ℕ} (hn : 1 < n) :
    IntegrableOn (fun E : ℝ => 1 / (1 + E) ^ n) (Ioi 0) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have h := integrableOn_add_rpow_Ioi_of_lt
    (a := -(n : ℝ)) (c := 0) (m := 1) (by linarith) (by norm_num)
  simpa only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, one_div, add_comm] using h

theorem energy_dual_tail_integrable (j : ℤ) :
    IntegrableOn (fun E => E / (1 + E) ^ 4 * referenceDensity j E)
      (Ioi (|(j : ℝ)| + 1)) := by
  have hs : Ioi (|(j : ℝ)| + 1) ⊆ Ioi (0 : ℝ) := by
    intro E hE
    have hj := abs_nonneg (j : ℝ)
    change |(j : ℝ)| + 1 < E at hE
    change 0 < E
    linarith
  apply ((integrableOn_one_div_one_add_pow (n := 3) (by norm_num)).mono_set hs).mono'
  · exact ((measurable_id.div ((measurable_const.add measurable_id).pow_const 4)).mul
      (measurable_referenceDensity j)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    have hE0 : 0 ≤ E := (hs hE).le
    have hp : 0 < 1 + E := by linarith
    rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg hE0 (pow_nonneg hp.le 4))
      (referenceDensity_nonneg j E))]
    calc
      E / (1 + E) ^ 4 * referenceDensity j E ≤ E / (1 + E) ^ 4 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (referenceDensity_le_one hE.le) (div_nonneg hE0 (pow_nonneg hp.le 4))
      _ ≤ 1 / (1 + E) ^ 3 := by
        rw [div_le_div_iff₀ (pow_pos hp 4) (pow_pos hp 3)]
        nlinarith [pow_nonneg hp.le 3]

theorem spin_dual_tail_integrable (j : ℤ) :
    IntegrableOn (fun E => (j : ℝ) ^ 2 / (1 + E) ^ 4 * referenceDensity j E)
      (Ioi (|(j : ℝ)| + 1)) := by
  have hs : Ioi (|(j : ℝ)| + 1) ⊆ Ioi (0 : ℝ) := by
    intro E hE
    have hj := abs_nonneg (j : ℝ)
    change |(j : ℝ)| + 1 < E at hE
    change 0 < E
    linarith
  have hi : IntegrableOn (fun E : ℝ => (j : ℝ) ^ 2 * (1 / (1 + E) ^ 4))
      (Ioi 0) := (integrableOn_one_div_one_add_pow (n := 4) (by norm_num)).const_mul _
  apply (hi.mono_set hs).mono'
  · exact ((measurable_const.div ((measurable_const.add measurable_id).pow_const 4)).mul
      (measurable_referenceDensity j)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    have hnonneg : 0 ≤ (j : ℝ) ^ 2 / (1 + E) ^ 4 := by positivity
    rw [Real.norm_of_nonneg (mul_nonneg hnonneg (referenceDensity_nonneg j E)),
      mul_one_div]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (referenceDensity_le_one hE.le) hnonneg

/-- In the scalar row, the energy moment cancels `dE/E` at the origin. -/
theorem scalar_energy_dual_integrable :
    IntegrableOn (fun E => E / (1 + E) ^ 4 * referenceDensity 0 E) (Ioi 0) := by
  apply (integrableOn_one_div_one_add_pow (n := 4) (by norm_num)).congr_fun
    _ measurableSet_Ioi
  intro E hE
  change 0 < E at hE
  dsimp
  rw [referenceDensity_zero hE.le]
  field_simp [ne_of_gt hE]

theorem energy_dual_reference_integrable (j : ℤ) :
    IntegrableOn (fun E => E / (1 + E) ^ 4 * referenceDensity j E)
      (Ioi |(j : ℝ)|) := by
  by_cases hj : j = 0
  · simpa [hj] using scalar_energy_dual_integrable
  have hr : 0 < |(j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
  have hc : ContinuousOn (fun E : ℝ => E / (1 + E) ^ 4)
      (Icc |(j : ℝ)| (|(j : ℝ)| + 2)) := by
    apply continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 4)
    intro E hE
    apply pow_ne_zero 4
    change 1 + E ≠ 0
    linarith [hE.1]
  have hedge : IntegrableOn (fun E => E / (1 + E) ^ 4 * referenceDensity j E)
      (Ioo |(j : ℝ)| (|(j : ℝ)| + 2)) := by
    simpa only [referenceDensity, mul_one_div, sq_abs] using
      nonzero_edge_continuous_numerator_integrableOn hr hc
  apply (hedge.union (energy_dual_tail_integrable j)).mono_set
  intro E hE
  by_cases he : E < |(j : ℝ)| + 2
  · exact Or.inl ⟨hE, he⟩
  · exact Or.inr (by change |(j : ℝ)| + 1 < E; linarith)

theorem spin_dual_reference_integrable (j : ℤ) :
    IntegrableOn (fun E => (j : ℝ) ^ 2 / (1 + E) ^ 4 * referenceDensity j E)
      (Ioi |(j : ℝ)|) := by
  by_cases hj : j = 0
  · simp [hj]
  have hr : 0 < |(j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
  have hc : ContinuousOn (fun E : ℝ => (j : ℝ) ^ 2 / (1 + E) ^ 4)
      (Icc |(j : ℝ)| (|(j : ℝ)| + 2)) := by
    apply continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 4)
    intro E hE
    apply pow_ne_zero 4
    change 1 + E ≠ 0
    linarith [hE.1]
  have hedge : IntegrableOn (fun E => (j : ℝ) ^ 2 / (1 + E) ^ 4 * referenceDensity j E)
      (Ioo |(j : ℝ)| (|(j : ℝ)| + 2)) := by
    simpa only [referenceDensity, mul_one_div, sq_abs] using
      nonzero_edge_continuous_numerator_integrableOn hr hc
  apply (hedge.union (spin_dual_tail_integrable j)).mono_set
  intro E hE
  by_cases he : E < |(j : ℝ)| + 2
  · exact Or.inl ⟨hE, he⟩
  · exact Or.inr (by change |(j : ℝ)| + 1 < E; linarith)

/-- The energy dual weight needed for weighted Cauchy–Schwarz in every physical row. -/
theorem energy_dual_integrable_referenceMeasure (j : ℤ) :
    Integrable (fun E => E / (1 + E) ^ 4) (referenceMeasure j) := by
  rw [referenceMeasure,
    integrable_withDensity_iff_integrable_smul'
      (measurable_referenceDensity j).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (referenceDensity_nonneg j _), smul_eq_mul, mul_comm,
    IntegrableOn] using energy_dual_reference_integrable j

/-- The spin dual weight needed for weighted Cauchy–Schwarz in every physical row. -/
theorem spin_dual_integrable_referenceMeasure (j : ℤ) :
    Integrable (fun E => (j : ℝ) ^ 2 / (1 + E) ^ 4) (referenceMeasure j) := by
  rw [referenceMeasure,
    integrable_withDensity_iff_integrable_smul'
      (measurable_referenceDensity j).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (referenceDensity_nonneg j _), smul_eq_mul, mul_comm,
    IntegrableOn] using spin_dual_reference_integrable j

end GapFamily.Analytic
