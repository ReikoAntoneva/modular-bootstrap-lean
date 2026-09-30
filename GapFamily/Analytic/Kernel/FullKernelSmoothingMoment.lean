import GapFamily.Analytic.Kernel.HigherKernelResponseMoment

/-!
# Square-root energy moments on the physical low band

The scalar reference measure is `dE/E`. A square-root energy zero is enough
for ordinary integrability, and its squared moment is the first energy moment.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace GapFamily.Analytic

private theorem hasDerivAt_two_sqrt {E : ℝ} (hE : 0 < E) :
    HasDerivAt (fun x : ℝ => 2 * Real.sqrt x) (1 / Real.sqrt E) E := by
  convert (Real.hasDerivAt_sqrt hE.ne').const_mul 2 using 1
  field_simp

private theorem inv_sqrt_intervalIntegrable {B : ℝ} (hB : 0 ≤ B) :
    IntervalIntegrable (fun E : ℝ => 1 / Real.sqrt E) volume 0 B := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (g := fun E : ℝ => 2 * Real.sqrt E)
  · fun_prop
  · simpa only [min_eq_left hB, max_eq_right hB] using
      (fun E (hE : E ∈ Ioo 0 B) => hasDerivAt_two_sqrt hE.1)
  · intro E hE
    positivity

private theorem integral_inv_sqrt {B : ℝ} (hB : 0 ≤ B) :
    (∫ E in Ioo 0 B, 1 / Real.sqrt E) = 2 * Real.sqrt B := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hB
    (f := fun E : ℝ => 2 * Real.sqrt E) (by fun_prop)
    (fun E hE => hasDerivAt_two_sqrt hE.1) (inv_sqrt_intervalIntegrable hB)
  rw [intervalIntegral.integral_of_le hB, integral_Ioc_eq_integral_Ioo] at h
  simpa using h

private theorem scalar_density_mul_sqrt {E : ℝ} (hE : 0 < E) :
    referenceDensity 0 E * Real.sqrt E = 1 / Real.sqrt E := by
  rw [referenceDensity_zero hE.le]
  have hs : Real.sqrt E ≠ 0 := (Real.sqrt_pos.mpr hE).ne'
  field_simp
  exact Real.sq_sqrt hE.le

/-- A square-root zero is ordinarily integrable at the scalar `dE/E` origin. -/
theorem lowBand_zero_sqrt_energy_integrable (B : ℝ) :
    Integrable (fun E : ℝ => Real.sqrt E)
      ((referenceMeasure 0).restrict (Ioo 0 B)) := by
  by_cases hB : 0 ≤ B
  · rw [show Ioo 0 B = Ioo |((0 : ℤ) : ℝ)| B by simp,
      lowBandReferenceMeasure_eq,
      integrable_withDensity_iff_integrable_smul'
        (measurable_referenceDensity 0).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [Int.cast_zero, abs_zero,
      ENNReal.toReal_ofReal (referenceDensity_nonneg 0 _), smul_eq_mul]
    have hi := (inv_sqrt_intervalIntegrable hB).1
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hi
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
    exact (scalar_density_mul_sqrt hE.1).symm
  · simp [Ioo_eq_empty_of_le (le_of_not_ge hB)]

/-- Exact ordinary square-root moment in the scalar row. -/
theorem lowBand_zero_integral_sqrt_energy {B : ℝ} (hB : 0 ≤ B) :
    (∫ E, Real.sqrt E ∂(referenceMeasure 0).restrict (Ioo 0 B)) =
      2 * Real.sqrt B := by
  rw [show Ioo 0 B = Ioo |((0 : ℤ) : ℝ)| B by simp,
    lowBandReferenceMeasure_eq, integral_withDensity_eq_integral_toReal_smul
      (measurable_referenceDensity 0).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [Int.cast_zero, abs_zero,
    ENNReal.toReal_ofReal (referenceDensity_nonneg 0 _), smul_eq_mul]
  rw [← integral_inv_sqrt hB]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  exact scalar_density_mul_sqrt hE.1

private theorem sqrt_energy_le_energy_of_nonzero {j : ℤ} (hj : j ≠ 0)
    {E : ℝ} (hE : |(j : ℝ)| ≤ E) : Real.sqrt E ≤ E := by
  have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
  exact Real.sqrt_le_self_iff.mpr (Or.inr (hj1.trans hE))

/-- Ordinary square-root energy integrability includes every nonzero edge
and the infinite scalar reference mass. -/
theorem lowBand_sqrt_energy_integrable (j : ℤ) (B : ℝ) :
    Integrable (fun E : ℝ => Real.sqrt E)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  by_cases hj : j = 0
  · simpa [hj] using lowBand_zero_sqrt_energy_integrable B
  apply (lowBand_energy_integrable j B).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg E)]
  exact sqrt_energy_le_energy_of_nonzero hj hE.1.le

private theorem integral_energy_le (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    (∫ E, E ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤ B := by
  by_cases hj : |(j : ℝ)| ≤ B
  · rw [lowBand_integral_energy j hj]
    exact (Real.sqrt_le_left hB).mpr (by nlinarith [sq_nonneg (j : ℝ)])
  · simp [Ioo_eq_empty_of_le (le_of_not_ge hj), hB]

/-- A uniform ordinary square-root moment bound requiring no scalar finite-mass assumption. -/
theorem lowBand_integral_sqrt_energy_le (j : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    (∫ E, Real.sqrt E ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤
      B + 2 * Real.sqrt B := by
  by_cases hj : j = 0
  · simp only [hj, Int.cast_zero, abs_zero, lowBand_zero_integral_sqrt_energy hB]
    linarith
  calc
    _ ≤ ∫ E, E ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
      apply integral_mono_ae (lowBand_sqrt_energy_integrable j B) (lowBand_energy_integrable j B)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
      exact sqrt_energy_le_energy_of_nonzero hj hE.1.le
    _ ≤ B := integral_energy_le j B hB
    _ ≤ B + 2 * Real.sqrt B := by linarith [Real.sqrt_nonneg B]

/-- The square-root coordinate is a genuine low-band `L²` function. -/
theorem lowBand_sqrt_energy_memLp (j : ℤ) (B : ℝ) :
    MemLp (fun E : ℝ => Real.sqrt E) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  apply (lowBand_energy_integrable j B).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  exact (Real.sq_sqrt ((abs_nonneg (j : ℝ)).trans hE.1.le)).symm

/-- Square-root moments of arbitrary low-band Hilbert data are ordinary integrals. -/
theorem lowBand_sqrt_energy_norm_integrable (j : ℤ) (B : ℝ)
    (f : LowBandRow j B) :
    Integrable (fun E => Real.sqrt E * ‖f E‖)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
  (lowBand_sqrt_energy_memLp j B).integrable_mul (Lp.memLp f).norm

/-- Cauchy--Schwarz controls the square-root moment by `sqrt B` times the row norm. -/
theorem lowBand_sqrt_energy_norm_integral_le (j : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandRow j B) :
    (∫ E, Real.sqrt E * ‖f E‖ ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) ≤
      Real.sqrt B * ‖f‖ := by
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall (fun E => Real.sqrt_nonneg E))
    (Filter.Eventually.of_forall (fun E => norm_nonneg (f E)))
    (by simpa using lowBand_sqrt_energy_memLp j B) (by simpa using (Lp.memLp f).norm)
  norm_num only [Real.rpow_two] at hc
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hc
  have hn : (∫ E, ‖f E‖ ^ 2 ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) =
      ‖f‖ ^ 2 := (lowBandRow_norm_sq_eq_integral (fun _ : Unit => j) B () f).symm
  have hs : (∫ E, (Real.sqrt E) ^ 2 ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) =
      ∫ E, E ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
    exact Real.sq_sqrt ((abs_nonneg (j : ℝ)).trans hE.1.le)
  rw [hn, hs, Real.sqrt_sq (norm_nonneg f)] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (integral_energy_le j B hB)) (norm_nonneg f))

end GapFamily.Analytic
