import GapFamily.Analytic.Kernel.HigherKernelResponseBound
import GapFamily.Analytic.Foundation.ReferenceMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Ordinary thermal integrability of the full arithmetic higher-kernel series. -/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory
open scoped Real

theorem integrableOn_energy_exp_neg {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun e : ℝ => e * Real.exp (-t * e)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1)
      (by norm_num) zero_lt_one ht)

theorem energy_exp_reference_tail_integrable (j : ℤ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun e : ℝ => (e * Real.exp (-t * e)) * referenceDensity j e)
      (Ioi (|(j : ℝ)| + 1)) := by
  have hs : Ioi (|(j : ℝ)| + 1) ⊆ Ioi (0 : ℝ) := by
    intro e he
    have hj := abs_nonneg (j : ℝ)
    change |(j : ℝ)| + 1 < e at he
    change 0 < e
    linarith
  apply ((integrableOn_energy_exp_neg ht).mono_set hs).mono'
  · exact ((continuous_id.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).measurable.mul
      (measurable_referenceDensity j)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
    have he0 : 0 ≤ e := (hs he).le
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg he0 (Real.exp_pos _).le)
      (referenceDensity_nonneg j e))]
    simpa using mul_le_mul_of_nonneg_left (referenceDensity_le_one he.le)
      (mul_nonneg he0 (Real.exp_pos (-t * e)).le)

theorem energy_exp_reference_integrable (j : ℤ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun e : ℝ => (e * Real.exp (-t * e)) * referenceDensity j e)
      (Ioi |(j : ℝ)|) := by
  by_cases hj : j = 0
  · subst j
    simp only [Int.cast_zero, abs_zero]
    have hi : IntegrableOn (fun e : ℝ => Real.exp (-t * e)) (Ioi 0) := by
      simpa only [Real.rpow_one, Real.rpow_zero, one_mul] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0)
          (by norm_num) zero_lt_one ht)
    apply hi.congr_fun _ measurableSet_Ioi
    intro e he
    dsimp only
    rw [referenceDensity_zero he.le]
    field_simp [ne_of_gt (show 0 < e from he)]
  have hr : 0 < |(j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
  have hedge : IntegrableOn
      (fun e : ℝ => (e * Real.exp (-t * e)) * referenceDensity j e)
      (Ioo |(j : ℝ)| (|(j : ℝ)| + 2)) := by
    simpa only [referenceDensity, mul_one_div, sq_abs, Pi.mul_apply, Function.comp_apply, id_eq] using
      (nonzero_edge_continuous_numerator_integrableOn (B := |(j : ℝ)| + 2) hr
        (continuous_id.mul (Real.continuous_exp.comp
          (continuous_const.mul continuous_id))).continuousOn)
  apply (hedge.union (energy_exp_reference_tail_integrable j ht)).mono_set
  intro e he
  by_cases h : e < |(j : ℝ)| + 2
  · exact Or.inl ⟨he, h⟩
  · exact Or.inr (by change |(j : ℝ)| + 1 < e; linarith)

theorem integrable_energy_exp_referenceMeasure (j : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun e : ℝ => e * Real.exp (-t * e)) (referenceMeasure j) := by
  rw [referenceMeasure,
    integrable_withDensity_iff_integrable_smul'
      (measurable_referenceDensity j).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (referenceDensity_nonneg j _), smul_eq_mul, mul_comm,
    IntegrableOn] using energy_exp_reference_integrable j ht

private theorem thermal_sqrt_growth_le (K : ℝ) {t e : ℝ}
    (ht : 0 < t) (he : 0 ≤ e) :
    K * Real.sqrt e ≤ t * e / 2 + K ^ 2 / (2 * t) := by
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * t by positivity)).mp
  calc
    (2 * t) * (K * Real.sqrt e) ≤ (t * Real.sqrt e) ^ 2 + K ^ 2 := by
      nlinarith [sq_nonneg (t * Real.sqrt e - K)]
    _ = (2 * t) * (t * e / 2 + K ^ 2 / (2 * t)) := by
      rw [mul_pow, Real.sq_sqrt he]
      field_simp

/-- A positive tilt absorbs arbitrary square-root exponential growth. -/
theorem thermal_exp_sqrt_le (K : ℝ) {t e : ℝ} (ht : 0 < t) (he : 0 ≤ e) :
    Real.exp (K * Real.sqrt e - t * e) ≤
      Real.exp (K ^ 2 / (2 * t)) * Real.exp (-(t / 2) * e) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [thermal_sqrt_growth_le K ht he]

/-- The energy factor cancels the scalar endpoint before the thermal estimate is used. -/
theorem integrable_energy_exp_sqrt_referenceMeasure (j : ℤ) (K : ℝ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun e : ℝ => e * Real.exp (K * Real.sqrt e - t * e))
      (referenceMeasure j) := by
  have hbase := (integrable_energy_exp_referenceMeasure j
    (show 0 < t / 2 by positivity)).const_mul (Real.exp (K ^ 2 / (2 * t)))
  apply hbase.mono'
  · exact (continuous_id.mul (Real.continuous_exp.comp
      ((continuous_const.mul Real.continuous_sqrt).sub
        (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · filter_upwards [referenceMeasure_ae_above_edge j] with e he
    have he0 : 0 ≤ e := (abs_nonneg _).trans he.le
    rw [Real.norm_of_nonneg (mul_nonneg he0 (Real.exp_pos _).le)]
    calc
      _ ≤ e * (Real.exp (K ^ 2 / (2 * t)) * Real.exp (-(t / 2) * e)) :=
        mul_le_mul_of_nonneg_left (thermal_exp_sqrt_le K ht he0) he0
      _ = _ := by ring

/-- The two chiral arguments are unchanged on interchanging input and output. -/
theorem higherKernelArgPlus_swap (j J : ℤ) (e E : ℂ) :
    higherKernelArgPlus j J e E = higherKernelArgPlus J j E e := by
  unfold higherKernelArgPlus
  ring

theorem higherKernelArgMinus_swap (j J : ℤ) (e E : ℂ) :
    higherKernelArgMinus j J e E = higherKernelArgMinus J j E e := by
  unfold higherKernelArgMinus
  ring

/-- Each denominator retains a factor of physical output energy, including spin zero. -/
theorem norm_higherKernelTerm_physical_output_le (j J : ℤ) (e : ℝ) (E : ℂ)
    (he : |(j : ℝ)| ≤ e) (n : ℕ) :
    ‖higherKernelTerm j J e E n‖ ≤
      (4 * π ^ 2 * (‖E‖ + |(J : ℝ)|) * e *
        Real.exp (8 * π * Real.sqrt ((‖E‖ + |(J : ℝ)|) * e))) /
          ((n : ℝ) + 1) ^ 2 := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hp := norm_higherKernelArg_sum_le J j E e he
  have hs := sqrt_norm_higherKernelArg_sum_le J j E e he
  rw [← higherKernelArgPlus_swap j J, ← higherKernelArgMinus_swap j J] at hp hs
  calc
    _ ≤ ((‖higherKernelArgPlus j J e E‖ + ‖higherKernelArgMinus j J e E‖) / 2 *
        Real.exp (Real.sqrt ‖higherKernelArgPlus j J e E‖ +
          Real.sqrt ‖higherKernelArgMinus j J e E‖)) / ((n : ℝ) + 1) ^ 2 :=
      norm_higherKernelTerm_le_exp_sqrt j J e E n
    _ ≤ ((8 * π ^ 2 * (‖E‖ + |(J : ℝ)|) * e) / 2 *
        Real.exp (8 * π * Real.sqrt ((‖E‖ + |(J : ℝ)|) * e))) /
          ((n : ℝ) + 1) ^ 2 := by
      gcongr
    _ = _ := by ring

/-- A real thermal tilt has the expected ordinary exponential norm. -/
theorem norm_exp_thermal (t e : ℝ) :
    ‖Complex.exp (-(t : ℂ) * (e : ℂ))‖ = Real.exp (-t * e) := by
  simp [Complex.norm_exp]

/-- A separated majorant for the thermally tilted arithmetic summand. -/
theorem norm_thermal_higherKernelTerm_le (j J : ℤ) (e : ℝ) (E : ℂ) (t : ℝ)
    (he : |(j : ℝ)| ≤ e) (n : ℕ) :
    ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * (2 * higherKernelTerm j J e E n)‖ ≤
      (8 * π ^ 2 * (‖E‖ + |(J : ℝ)|) *
        (e * Real.exp ((8 * π * Real.sqrt (‖E‖ + |(J : ℝ)|)) * Real.sqrt e - t * e))) *
          (1 / ((n : ℝ) + 1) ^ 2) := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  rw [norm_mul, norm_mul, norm_exp_thermal, Complex.norm_ofNat]
  calc
    _ ≤ Real.exp (-t * e) * (2 *
        ((4 * π ^ 2 * (‖E‖ + |(J : ℝ)|) * e *
          Real.exp (8 * π * Real.sqrt ((‖E‖ + |(J : ℝ)|) * e))) /
            ((n : ℝ) + 1) ^ 2)) := by
      gcongr
      exact norm_higherKernelTerm_physical_output_le j J e E he n
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ ‖E‖ + |(J : ℝ)|)]
      simp only [sub_eq_add_neg, mul_assoc, Real.exp_add]
      ring

/-- The common thermal envelope for all denominators. -/
def higherKernelThermalEnvelope (J : ℤ) (E : ℂ) (t e : ℝ) : ℝ :=
  8 * π ^ 2 * (‖E‖ + |(J : ℝ)|) *
    (e * Real.exp ((8 * π * Real.sqrt (‖E‖ + |(J : ℝ)|)) * Real.sqrt e - t * e))

theorem integrable_higherKernelThermalEnvelope (j J : ℤ) (E : ℂ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (higherKernelThermalEnvelope J E t) (referenceMeasure j) :=
  (integrable_energy_exp_sqrt_referenceMeasure j _ ht).const_mul _

/-- The same envelope controls the actual infinite higher kernel. -/
theorem norm_thermal_higherKernel_le (j J : ℤ) (e : ℝ) (E : ℂ) (t : ℝ)
    (he : |(j : ℝ)| ≤ e) :
    ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * higherKernel j J e E‖ ≤
      2 * higherKernelThermalEnvelope J E t e := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have henv : 0 ≤ higherKernelThermalEnvelope J E t e := by
    unfold higherKernelThermalEnvelope
    positivity
  have hs := ((summable_higherKernelTerm j J e E).mul_left 2).mul_left
    (Complex.exp (-(t : ℂ) * (e : ℂ)))
  have hbound := summable_one_div_nat_sq.mul_left (higherKernelThermalEnvelope J E t e)
  calc
    _ = ‖∑' n, Complex.exp (-(t : ℂ) * (e : ℂ)) *
        (2 * higherKernelTerm j J e E n)‖ := by
      simp only [higherKernel, tsum_mul_left]
    _ ≤ ∑' n, ‖Complex.exp (-(t : ℂ) * (e : ℂ)) *
        (2 * higherKernelTerm j J e E n)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, higherKernelThermalEnvelope J E t e *
        (1 / ((n : ℝ) + 1) ^ 2) :=
      Summable.tsum_le_tsum (fun n => norm_thermal_higherKernelTerm_le j J e E t he n)
        hs.norm hbound
    _ = higherKernelThermalEnvelope J E t e * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 :=
      tsum_mul_left
    _ ≤ higherKernelThermalEnvelope J E t e * 2 :=
      mul_le_mul_of_nonneg_left tsum_one_div_nat_sq_le_two henv
    _ = _ := mul_comm _ _

/-- The full higher kernel has an ordinary absolutely convergent thermal transform. -/
theorem integrable_thermal_higherKernel (j J : ℤ) (E : ℂ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun e : ℝ => Complex.exp (-(t : ℂ) * (e : ℂ)) *
      higherKernel j J e E) (referenceMeasure j) := by
  apply ((integrable_higherKernelThermalEnvelope j J E ht).const_mul 2).mono'
  · have hExp : Continuous (fun e : ℝ => Complex.exp (-(t : ℂ) * (e : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact (hExp.mul ((continuous_higherKernel j J).comp
      (Complex.continuous_ofReal.prodMk continuous_const))).aestronglyMeasurable
  · filter_upwards [referenceMeasure_ae_above_edge j] with e he
    exact norm_thermal_higherKernel_le j J e E t he.le

/-- Every denominator term has an ordinary absolutely convergent thermal transform. -/
theorem integrable_thermal_higherKernelTerm (j J : ℤ) (E : ℂ)
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Integrable (fun e : ℝ => Complex.exp (-(t : ℂ) * (e : ℂ)) *
      (2 * higherKernelTerm j J e E n)) (referenceMeasure j) := by
  apply ((integrable_higherKernelThermalEnvelope j J E ht).mul_const
    (1 / ((n : ℝ) + 1) ^ 2)).mono'
  · have hExp : Continuous (fun e : ℝ => Complex.exp (-(t : ℂ) * (e : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact (hExp.mul (continuous_const.mul ((continuous_higherKernelTerm j J n).comp
      (Complex.continuous_ofReal.prodMk continuous_const)))).aestronglyMeasurable
  · filter_upwards [referenceMeasure_ae_above_edge j] with e he
    exact norm_thermal_higherKernelTerm_le j J e E t he.le n

/-- Absolute integrals of the intact higher terms are summable in the denominator. -/
theorem summable_integral_norm_thermal_higherKernelTerm (j J : ℤ) (E : ℂ)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ∫ e : ℝ,
      ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * (2 * higherKernelTerm j J e E n)‖
        ∂referenceMeasure j) := by
  have henv := integrable_higherKernelThermalEnvelope j J E ht
  apply (summable_one_div_nat_sq.mul_left
    (∫ e, higherKernelThermalEnvelope J E t e ∂referenceMeasure j)).of_nonneg_of_le
  · intro n
    exact integral_nonneg (fun _ => norm_nonneg _)
  · intro n
    calc
      _ ≤ ∫ e, higherKernelThermalEnvelope J E t e *
          (1 / ((n : ℝ) + 1) ^ 2) ∂referenceMeasure j := by
        apply integral_mono_ae (integrable_thermal_higherKernelTerm j J E ht n).norm
          (henv.mul_const _)
        filter_upwards [referenceMeasure_ae_above_edge j] with e he
        exact norm_thermal_higherKernelTerm_le j J e E t he.le n
      _ = _ := integral_mul_const _ _

/-- The full higher-kernel thermal integral is the sum of its ordinary term integrals. -/
theorem integral_thermal_higherKernel_eq_tsum (j J : ℤ) (E : ℂ)
    {t : ℝ} (ht : 0 < t) :
    (∫ e : ℝ, Complex.exp (-(t : ℂ) * (e : ℂ)) * higherKernel j J e E
      ∂referenceMeasure j) =
      ∑' n : ℕ, ∫ e : ℝ, Complex.exp (-(t : ℂ) * (e : ℂ)) *
        (2 * higherKernelTerm j J e E n) ∂referenceMeasure j := by
  rw [integral_tsum_of_summable_integral_norm
    (fun n => integrable_thermal_higherKernelTerm j J E ht n)
    (summable_integral_norm_thermal_higherKernelTerm j J E ht)]
  simp only [higherKernel, tsum_mul_left]

end GapFamily.Analytic
