import GapFamily.Analytic.Kernel.LowBandOperator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace GapFamily.Analytic

private theorem hasDerivAt_sqrt_sq_sub {r E : ℝ} (hr : 0 ≤ r) (hE : r < E) :
    HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 - r ^ 2))
      (E / Real.sqrt (E ^ 2 - r ^ 2)) E := by
  have hpos : 0 < E ^ 2 - r ^ 2 := by nlinarith
  convert (((hasDerivAt_id E).pow 2).sub_const (r ^ 2)).sqrt hpos.ne' using 1
  simp only [Pi.pow_apply, id_eq]
  norm_num
  field_simp

private theorem energy_div_sqrt_intervalIntegrable {r B : ℝ} (hr : 0 ≤ r) (hB : r ≤ B) :
    IntervalIntegrable (fun E : ℝ => E / Real.sqrt (E ^ 2 - r ^ 2)) volume r B := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (g := fun E : ℝ => Real.sqrt (E ^ 2 - r ^ 2))
  · fun_prop
  · simpa only [min_eq_left hB, max_eq_right hB] using
      (fun E (hE : E ∈ Ioo r B) => hasDerivAt_sqrt_sq_sub hr hE.1)
  · intro E hE
    have hE' : E ∈ Ioo r B := by simpa only [min_eq_left hB, max_eq_right hB] using hE
    exact div_nonneg (hr.trans hE'.1.le) (Real.sqrt_nonneg _)

private theorem integral_energy_div_sqrt {r B : ℝ} (hr : 0 ≤ r) (hB : r ≤ B) :
    (∫ E in Ioo r B, E / Real.sqrt (E ^ 2 - r ^ 2)) = Real.sqrt (B ^ 2 - r ^ 2) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hB
    (f := fun E : ℝ => Real.sqrt (E ^ 2 - r ^ 2))
    (by fun_prop) (fun E hE => hasDerivAt_sqrt_sq_sub hr hE.1)
    (energy_div_sqrt_intervalIntegrable hr hB)
  rw [intervalIntegral.integral_of_le hB, integral_Ioc_eq_integral_Ioo] at h
  simpa using h

theorem lowBandReferenceMeasure_eq (j : ℤ) (B : ℝ) :
    (referenceMeasure j).restrict (Ioo |(j : ℝ)| B) =
      (volume.restrict (Ioo |(j : ℝ)| B)).withDensity
        (fun E => ENNReal.ofReal (referenceDensity j E)) := by
  rw [referenceMeasure, restrict_withDensity measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr Ioo_subset_Ioi_self]

/-- The energy factor makes the ordinary low-band mass integrable even at scalar spin. -/
theorem lowBand_energy_integrable (j : ℤ) (B : ℝ) :
    Integrable (fun E : ℝ => E) ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  by_cases hB : |(j : ℝ)| ≤ B
  · rw [lowBandReferenceMeasure_eq,
      integrable_withDensity_iff_integrable_smul'
        (measurable_referenceDensity j).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hi := (energy_div_sqrt_intervalIntegrable (abs_nonneg (j : ℝ)) hB).1
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hi
    simp_rw [ENNReal.toReal_ofReal (referenceDensity_nonneg j _)]
    simpa only [smul_eq_mul, referenceDensity, sq_abs, one_div, mul_comm,
      div_eq_mul_inv, one_mul, IntegrableOn] using hi
  · simp [Ioo_eq_empty_of_le (le_of_not_ge hB)]

/-- Exact first moment of the physical reference measure on a nonempty low band. -/
theorem lowBand_integral_energy (j : ℤ) {B : ℝ} (hB : |(j : ℝ)| ≤ B) :
    (∫ E, E ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) =
      Real.sqrt (B ^ 2 - (j : ℝ) ^ 2) := by
  rw [lowBandReferenceMeasure_eq, integral_withDensity_eq_integral_toReal_smul
    (measurable_referenceDensity j).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (referenceDensity_nonneg j _)]
  simpa only [smul_eq_mul, referenceDensity, sq_abs, one_div, mul_comm,
    div_eq_mul_inv, one_mul] using
    integral_energy_div_sqrt (abs_nonneg (j : ℝ)) hB

/-- The second energy moment has a spin-independent quadratic bound. -/
theorem lowBand_energy_sq_integrable_le (j : ℤ) {B : ℝ} (hB : 0 ≤ B) :
    Integrable (fun E : ℝ => E ^ 2)
        ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ∧
      (∫ E, E ^ 2 ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤ B ^ 2 := by
  have hdom := (lowBand_energy_integrable j B).const_mul B
  have hpoint : ∀ᵐ E ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B),
      ‖E ^ 2‖ ≤ B * E := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
    rw [Real.norm_of_nonneg (sq_nonneg E)]
    have hE0 : 0 ≤ E := (abs_nonneg (j : ℝ)).trans hE.1.le
    nlinarith [mul_nonneg hE0 (sub_nonneg.mpr hE.2.le)]
  have hi : Integrable (fun E : ℝ => E ^ 2)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
    hdom.mono' (by fun_prop) hpoint
  refine ⟨hi, ?_⟩
  by_cases hedge : |(j : ℝ)| ≤ B
  · calc
      _ ≤ ∫ E, B * E ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
        apply integral_mono_ae hi hdom
        exact hpoint.mono fun E hE => (le_abs_self _).trans hE
      _ = B * Real.sqrt (B ^ 2 - (j : ℝ) ^ 2) := by
        rw [integral_const_mul, lowBand_integral_energy j hedge]
      _ ≤ B * B := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact (Real.sqrt_le_left hB).mpr (by nlinarith [sq_nonneg (j : ℝ)])
      _ = B ^ 2 := by ring
  · simp [Ioo_eq_empty_of_le (le_of_not_ge hedge), sq_nonneg B]

/-- The energy coordinate belongs to the actual low-band `L²` space, uniformly in spin. -/
theorem lowBand_energy_memLp (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    MemLp (fun E : ℝ => E) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    (lowBand_energy_sq_integrable_le j hB).1

/-- Ordinary first energy moments of actual low-band data are finite. -/
theorem lowBand_energy_norm_integrable (j : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandRow j B) :
    Integrable (fun E => E * ‖f E‖)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  (lowBand_energy_memLp j B hB).integrable_mul (Lp.memLp f).norm

/-- Cauchy--Schwarz gives a uniform first energy moment bound with no scalar mass assumption. -/
theorem lowBand_energy_norm_integral_le (j : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandRow j B) :
    (∫ E, E * ‖f E‖ ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤ B * ‖f‖ := by
  have hE := lowBand_energy_memLp j B hB
  have hpos : ∀ᵐ E ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B), 0 ≤ E := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
    exact (abs_nonneg (j : ℝ)).trans hE.1.le
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    hpos (Filter.Eventually.of_forall (fun E => norm_nonneg (f E)))
    (by simpa using hE) (by simpa using (Lp.memLp f).norm)
  norm_num only [Real.rpow_two] at hc
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hc
  have hn : (∫ E, ‖f E‖ ^ 2 ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) =
      ‖f‖ ^ 2 := by
    exact (lowBandRow_norm_sq_eq_integral (fun _ : Unit => j) B () f).symm
  rw [hn, Real.sqrt_sq (norm_nonneg f)] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    ((Real.sqrt_le_left hB).mpr (lowBand_energy_sq_integrable_le j hB).2) (norm_nonneg f))

end GapFamily.Analytic
