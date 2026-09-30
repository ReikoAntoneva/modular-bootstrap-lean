import GapFamily.Construction.FiniteRepairState
import GapFamily.Construction.PermanentSpectrumRemainderDensity

/-! Exact ordinary remainder rows from the concrete finite repair state. -/

noncomputable section
namespace GapFamily.Construction.FiniteRepairState
open Set Filter MeasureTheory Real Analytic

/-- Genuine thermal integrability already makes the stored numerator
measurable: the nonvanishing exponential weight can be removed. -/
theorem aestronglyMeasurable_numerator (s : FiniteRepairState)
    (hi : s.ThermalIntegrable) (j : ℤ) :
    AEStronglyMeasurable (s.numerator j) (referenceMeasure j) := by
  have hm := continuous_exp.aestronglyMeasurable.mul (hi j 1 zero_lt_one).aestronglyMeasurable
  apply hm.congr
  apply Eventually.of_forall
  intro E
  change exp E * (exp (-1 * E) * s.numerator j E) = s.numerator j E
  rw [neg_one_mul, exp_neg, ← mul_assoc, mul_inv_cancel₀ (exp_ne_zero _), one_mul]

/-- Every ordinary physical tail row of a genuine state is integrable. -/
theorem integrableOn_numerator_thermal (s : FiniteRepairState)
    (hi : s.ThermalIntegrable) (T : ℝ) (j : ℤ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun E => exp (-t * E) * s.numerator j E)
      (Ici (max T |(j : ℝ)|)) (referenceMeasure j) :=
  (hi j t ht).integrableOn

/-- Clearing a front removes the stored continuum below every smaller cutoff
on the actual physical support. -/
theorem numerator_zero_below_cutoff_ae (s : FiniteRepairState) (hc : s.Cleared)
    (T R : ℝ) (j : ℤ) (hR : R ≤ s.front j) :
    ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      E < R → s.numerator j E = 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ici] with E hE
  intro hER
  exact hc j E ((le_max_right T |(j : ℝ)|).trans hE) (hER.trans_le hR)

/-- The unprocessed continuum signed mass is exactly the ordinary physical
tail-density integral. No independent Fourier-decomposition premise is used. -/
theorem continuumThermalOutput_univ_eq_tailDensityThermalRow
    (s : FiniteRepairState) (hi : s.ThermalIntegrable) (hc : s.Cleared)
    (T : ℝ) (j : ℤ) (hfront : T ≤ s.front j) {t : ℝ} (ht : 0 < t) :
    s.continuumThermalOutput j t univ = tailDensityThermalRow T t s.numerator j := by
  rw [continuumThermalOutput, withDensityᵥ_apply (hi j t ht) MeasurableSet.univ,
    setIntegral_univ, tailDensityThermalRow]
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [referenceMeasure_ae_above_edge j] with E hE
  intro hout
  have hET : E < T := lt_of_not_ge fun hTE => hout (max_le hTE hE.le)
  rw [hc j E hE.le (hET.trans_le hfront), mul_zero]

end GapFamily.Construction.FiniteRepairState
