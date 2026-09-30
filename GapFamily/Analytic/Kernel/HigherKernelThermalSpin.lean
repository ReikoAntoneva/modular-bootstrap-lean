import GapFamily.Analytic.Kernel.HigherKernelThermal
import GapFamily.Analytic.Kernel.HigherKernelResponseMoment

/-! Absolute thermal summability of the actual higher kernel over all integer spins. -/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory
open scoped Real

theorem summable_int_polynomial_exp_abs (A B : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => (A * |(j : ℝ)| + B) * Real.exp (-t * |(j : ℝ)|)) := by
  have hn : Summable (fun n : ℕ => (A * (n : ℝ) + B) * Real.exp (-t * (n : ℝ))) := by
    have h₁ := (Real.summable_pow_mul_exp_neg_nat_mul 1 ht).mul_left A
    have h₀ := (Real.summable_pow_mul_exp_neg_nat_mul 0 ht).mul_left B
    simpa only [pow_one, pow_zero, one_mul, mul_add, add_mul, mul_assoc] using h₁.add h₀
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [Int.cast_natCast, Nat.abs_cast] using hn
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast] using hn

private theorem integral_reference_eq_density (j : ℤ) (f : ℝ → ℝ) :
    (∫ e, f e ∂referenceMeasure j) =
      ∫ e in Ioi |(j : ℝ)|, f e * referenceDensity j e := by
  rw [referenceMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_referenceDensity j).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (referenceDensity_nonneg j _), smul_eq_mul, mul_comm]

private theorem integral_lowBand_reference_eq_density (j : ℤ) (B : ℝ) (f : ℝ → ℝ) :
    (∫ e, f e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) =
      ∫ e in Ioo |(j : ℝ)| B, f e * referenceDensity j e := by
  rw [lowBandReferenceMeasure_eq, integral_withDensity_eq_integral_toReal_smul
    (measurable_referenceDensity j).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (referenceDensity_nonneg j _), smul_eq_mul, mul_comm]

private theorem thermal_split_bound {t e r : ℝ} (ht : 0 < t) (he : r ≤ e) :
    Real.exp (-t * e) ≤ Real.exp (-(t / 2) * r) * Real.exp (-(t / 2) * e) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The energy-weighted mass on the first unit interval decays exponentially in the spin. -/
theorem integral_energy_exp_reference_edge_le (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (∫ e, e * Real.exp (-t * e)
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (|(j : ℝ)| + 1))) ≤
        (|(j : ℝ)| + 1) * Real.exp (-t * |(j : ℝ)|) := by
  have hB : |(j : ℝ)| ≤ |(j : ℝ)| + 1 := by linarith
  calc
    _ ≤ ∫ e, Real.exp (-t * |(j : ℝ)|) * e
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (|(j : ℝ)| + 1)) := by
      apply integral_mono_ae (integrable_energy_exp_referenceMeasure j ht).integrableOn
        ((lowBand_energy_integrable j _).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      have he0 : 0 ≤ e := (abs_nonneg _).trans he.1.le
      calc
        _ ≤ e * Real.exp (-t * |(j : ℝ)|) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonpos_left he.1.le (by linarith))) he0
        _ = _ := mul_comm _ _
    _ = Real.exp (-t * |(j : ℝ)|) *
        Real.sqrt ((|(j : ℝ)| + 1) ^ 2 - (j : ℝ) ^ 2) := by
      rw [integral_const_mul, lowBand_integral_energy j hB]
    _ ≤ Real.exp (-t * |(j : ℝ)|) * (|(j : ℝ)| + 1) := by
      gcongr
      exact (Real.sqrt_le_left (by positivity)).mpr (by nlinarith [sq_nonneg (j : ℝ)])
    _ = _ := mul_comm _ _

/-- Beyond the first unit interval, the reference density is at most one. -/
theorem integral_energy_exp_reference_tail_le (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (∫ e in Ioi (|(j : ℝ)| + 1),
      (e * Real.exp (-t * e)) * referenceDensity j e) ≤
        Real.exp (-(t / 2) * |(j : ℝ)|) *
          ∫ e in Ioi (0 : ℝ), e * Real.exp (-(t / 2) * e) := by
  have hsub : Ioi (|(j : ℝ)| + 1) ⊆ Ioi (0 : ℝ) := by
    intro e he
    have hj := abs_nonneg (j : ℝ)
    change |(j : ℝ)| + 1 < e at he
    change 0 < e
    linarith
  have hbase := integrableOn_energy_exp_neg (show 0 < t / 2 by positivity)
  calc
    _ ≤ ∫ e in Ioi (|(j : ℝ)| + 1),
        Real.exp (-(t / 2) * |(j : ℝ)|) * (e * Real.exp (-(t / 2) * e)) := by
      apply integral_mono_ae (energy_exp_reference_tail_integrable j ht)
        ((hbase.mono_set hsub).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
      have he0 : 0 ≤ e := (hsub he).le
      calc
        _ ≤ e * Real.exp (-t * e) := by
          exact mul_le_of_le_one_right (mul_nonneg he0 (Real.exp_pos _).le)
            (referenceDensity_le_one he.le)
        _ ≤ e * (Real.exp (-(t / 2) * |(j : ℝ)|) * Real.exp (-(t / 2) * e)) :=
          mul_le_mul_of_nonneg_left (thermal_split_bound ht
            (le_trans (by linarith : |(j : ℝ)| ≤ |(j : ℝ)| + 1) he.le)) he0
        _ = _ := by ring
    _ = Real.exp (-(t / 2) * |(j : ℝ)|) *
        ∫ e in Ioi (|(j : ℝ)| + 1), e * Real.exp (-(t / 2) * e) := by
      rw [integral_const_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply setIntegral_mono_set hbase
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
        exact mul_nonneg he.le (Real.exp_pos _).le
      · exact Filter.Eventually.of_forall fun e he => hsub he

/-- A polynomial times exponential controls the thermal reference mass uniformly in spin. -/
theorem integral_energy_exp_referenceMeasure_le (j : ℤ) {t : ℝ} (ht : 0 < t) :
    (∫ e, e * Real.exp (-t * e) ∂referenceMeasure j) ≤
      (|(j : ℝ)| + 1) * Real.exp (-t * |(j : ℝ)|) +
        Real.exp (-(t / 2) * |(j : ℝ)|) *
          ∫ e in Ioi (0 : ℝ), e * Real.exp (-(t / 2) * e) := by
  have hB : |(j : ℝ)| ≤ |(j : ℝ)| + 1 := by linarith
  have hi := energy_exp_reference_integrable j ht
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi hB))
  rw [intervalIntegral.integral_of_le hB, integral_Ioc_eq_integral_Ioo] at hsplit
  rw [integral_reference_eq_density, ← hsplit,
    ← integral_lowBand_reference_eq_density]
  exact add_le_add (integral_energy_exp_reference_edge_le j ht)
    (integral_energy_exp_reference_tail_le j ht)

/-- Energy-weighted thermal reference mass is summable over every integer spin. -/
theorem summable_integral_energy_exp_referenceMeasure {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ e, e * Real.exp (-t * e) ∂referenceMeasure j) := by
  have hedge : Summable (fun j : ℤ => (|(j : ℝ)| + 1) *
      Real.exp (-t * |(j : ℝ)|)) := by
    simpa only [one_mul] using summable_int_polynomial_exp_abs 1 1 ht
  have htail : Summable (fun j : ℤ => Real.exp (-(t / 2) * |(j : ℝ)|) *
      ∫ e in Ioi (0 : ℝ), e * Real.exp (-(t / 2) * e)) := by
    simpa only [zero_mul, mul_zero, zero_add, add_zero, mul_comm] using
      summable_int_polynomial_exp_abs 0
        (∫ e in Ioi (0 : ℝ), e * Real.exp (-(t / 2) * e))
        (show 0 < t / 2 by positivity)
  apply (hedge.add htail).of_nonneg_of_le
  · intro j
    apply integral_nonneg_of_ae
    filter_upwards [referenceMeasure_ae_above_edge j] with e he
    exact mul_nonneg ((abs_nonneg _).trans he.le) (Real.exp_pos _).le
  · exact fun j => integral_energy_exp_referenceMeasure_le j ht

/-- Square-root exponential growth remains absolutely integrable after summing all spins. -/
theorem summable_integral_energy_exp_sqrt_referenceMeasure (K : ℝ)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ =>
      ∫ e, e * Real.exp (K * Real.sqrt e - t * e) ∂referenceMeasure j) := by
  apply ((summable_integral_energy_exp_referenceMeasure
    (show 0 < t / 2 by positivity)).mul_left (Real.exp (K ^ 2 / (2 * t)))).of_nonneg_of_le
  · intro j
    apply integral_nonneg_of_ae
    filter_upwards [referenceMeasure_ae_above_edge j] with e he
    exact mul_nonneg ((abs_nonneg _).trans he.le) (Real.exp_pos _).le
  · intro j
    calc
      _ ≤ ∫ e, Real.exp (K ^ 2 / (2 * t)) * (e * Real.exp (-(t / 2) * e))
          ∂referenceMeasure j := by
        apply integral_mono_ae (integrable_energy_exp_sqrt_referenceMeasure j K ht)
          ((integrable_energy_exp_referenceMeasure j
            (show 0 < t / 2 by positivity)).const_mul _)
        filter_upwards [referenceMeasure_ae_above_edge j] with e he
        have he0 : 0 ≤ e := (abs_nonneg _).trans he.le
        calc
          _ ≤ e * (Real.exp (K ^ 2 / (2 * t)) * Real.exp (-(t / 2) * e)) :=
            mul_le_mul_of_nonneg_left (thermal_exp_sqrt_le K ht he0) he0
          _ = _ := by ring
      _ = _ := integral_const_mul _ _

/-- The intact higher-kernel thermal output is absolutely summable over all output spins. -/
theorem summable_integral_norm_thermal_higherKernel_spin (J : ℤ) (E : ℂ)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ e : ℝ,
      ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * higherKernel j J e E‖ ∂referenceMeasure j) := by
  have hs := (summable_integral_energy_exp_sqrt_referenceMeasure
    (8 * Real.pi * Real.sqrt (‖E‖ + |(J : ℝ)|)) ht).mul_left
      (2 * (8 * Real.pi ^ 2 * (‖E‖ + |(J : ℝ)|)))
  apply hs.of_nonneg_of_le
  · intro j
    exact integral_nonneg fun _ => norm_nonneg _
  · intro j
    calc
      _ ≤ ∫ e, 2 * higherKernelThermalEnvelope J E t e ∂referenceMeasure j := by
        apply integral_mono_ae (integrable_thermal_higherKernel j J E ht).norm
          ((integrable_higherKernelThermalEnvelope j J E ht).const_mul 2)
        filter_upwards [referenceMeasure_ae_above_edge j] with e he
        exact norm_thermal_higherKernel_le j J e E t he.le
      _ = _ := by
        simp only [higherKernelThermalEnvelope, integral_const_mul, mul_assoc]

end GapFamily.Analytic
