import GapFamily.Analytic.Transform.LaplaceWeight
import GapFamily.Analytic.Foundation.ReferenceDualMoment
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Ordinary moments controlled by the weighted energy norm

The square-root energy and spin moments in the weak kernel estimate are
ordinary integrals, bounded by Cauchy--Schwarz in the actual weighted row.
-/

noncomputable section

open MeasureTheory Real Set

namespace GapFamily.Analytic

theorem referenceMeasure_absolutelyContinuous_energySpace (j : ℤ) :
    referenceMeasure j ≪ energySpaceMeasure j := by
  apply withDensity_absolutelyContinuous'
  · exact (by fun_prop : Measurable (fun E : ℝ => ENNReal.ofReal ((1 + E) ^ 4))).aemeasurable
  · filter_upwards [referenceMeasure_ae_above_edge j] with E hE
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    have hE0 : 0 < E := (abs_nonneg _).trans_lt hE
    positivity

theorem energy_integral_norm_sq (j : ℤ) (f : ℝ → ℂ) :
    (∫ E, ‖f E‖ ^ 2 ∂energySpaceMeasure j) =
      ∫ E, ((1 + E) ^ 2 * ‖f E‖) ^ 2 ∂referenceMeasure j := by
  rw [energySpaceMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop : Measurable (fun E : ℝ => ENNReal.ofReal ((1 + E) ^ 4)))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with E
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  ring

theorem weightedNorm_memLp (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) :
    MemLp (fun E => (1 + E) ^ 2 * ‖f E‖) 2 (referenceMeasure j) := by
  have hfm := hf.aestronglyMeasurable.mono_ac (referenceMeasure_absolutelyContinuous_energySpace j)
  apply (memLp_two_iff_integrable_sq
    (((continuous_const.add continuous_id).pow 2).measurable.aestronglyMeasurable.mul hfm.norm)).mpr
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  rw [energySpaceMeasure, integrable_withDensity_iff_integrable_smul'
    (by fun_prop : Measurable (fun E : ℝ => ENNReal.ofReal ((1 + E) ^ 4)))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hi
  apply hi.congr
  filter_upwards with E
  change (ENNReal.ofReal ((1 + E) ^ 4)).toReal • ‖f E‖ ^ 2 =
    ((1 + E) ^ 2 * ‖f E‖) ^ 2
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  ring

theorem dualWeight_memLp (j : ℤ) {u : ℝ → ℝ} (hu : Measurable u)
    (hint : Integrable (fun E => u E ^ 2 / (1 + E) ^ 4) (referenceMeasure j)) :
    MemLp (fun E => u E / (1 + E) ^ 2) 2 (referenceMeasure j) := by
  apply (memLp_two_iff_integrable_sq
    (hu.div ((measurable_const.add measurable_id).pow_const 2)).aestronglyMeasurable).mpr
  apply hint.congr
  filter_upwards with E
  change u E ^ 2 / (1 + E) ^ 4 = (u E / (1 + E) ^ 2) ^ 2
  rw [div_pow]
  ring

/-- The actual Cauchy--Schwarz moment bound, with its required ordinary integrability. -/
theorem weighted_moment_cauchy (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) {u : ℝ → ℝ} (hu : Measurable u)
    (hpos : ∀ᵐ E ∂referenceMeasure j, 0 ≤ u E)
    (hint : Integrable (fun E => u E ^ 2 / (1 + E) ^ 4) (referenceMeasure j)) :
    Integrable (fun E => u E * ‖f E‖) (referenceMeasure j) ∧
      (∫ E, u E * ‖f E‖ ∂referenceMeasure j) ≤
        sqrt (∫ E, u E ^ 2 / (1 + E) ^ 4 ∂referenceMeasure j) *
          sqrt (∫ E, ‖f E‖ ^ 2 ∂energySpaceMeasure j) := by
  have hv := dualWeight_memLp j hu hint
  have hw := weightedNorm_memLp j hf
  have heq : (fun E => u E / (1 + E) ^ 2 * ((1 + E) ^ 2 * ‖f E‖)) =ᵐ[
      referenceMeasure j] (fun E => u E * ‖f E‖) := by
    filter_upwards [referenceMeasure_ae_above_edge j] with E hE
    have hE0 := (abs_nonneg (j : ℝ)).trans_lt hE
    have hn : (1 + E) ^ 2 ≠ 0 := by positivity
    field_simp
  refine ⟨(hv.integrable_mul hw).congr heq, ?_⟩
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    (show ∀ᵐ E ∂referenceMeasure j, 0 ≤ u E / (1 + E) ^ 2 from
      hpos.mono (fun E hE => div_nonneg hE (sq_nonneg _)))
    (Filter.Eventually.of_forall (fun E => mul_nonneg (sq_nonneg (1 + E)) (norm_nonneg (f E))))
    (by simpa using hv) (by simpa using hw)
  rw [integral_congr_ae heq] at hc
  norm_num only [Real.rpow_two, show (1 : ℝ) / 2 = 1 / 2 from rfl] at hc
  rw [← sqrt_eq_rpow, ← sqrt_eq_rpow, ← energy_integral_norm_sq j f] at hc
  convert hc using 1
  congr 2
  apply integral_congr_ae
  filter_upwards with E
  rw [div_pow]
  ring

/-- The ordinary square-root energy moment is finite and controlled by the weighted norm. -/
theorem sqrtEnergy_moment_cauchy (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) :
    Integrable (fun E => sqrt E * ‖f E‖) (referenceMeasure j) ∧
      (∫ E, sqrt E * ‖f E‖ ∂referenceMeasure j) ≤
        sqrt (∫ E, E / (1 + E) ^ 4 ∂referenceMeasure j) *
          sqrt (∫ E, ‖f E‖ ^ 2 ∂energySpaceMeasure j) := by
  have heq : (fun E : ℝ => E / (1 + E) ^ 4) =ᵐ[referenceMeasure j]
      (fun E => sqrt E ^ 2 / (1 + E) ^ 4) := by
    filter_upwards [referenceMeasure_ae_above_edge j] with E hE
    rw [sq_sqrt ((abs_nonneg _).trans hE.le)]
  have h := weighted_moment_cauchy j hf Real.continuous_sqrt.measurable
    (Filter.Eventually.of_forall Real.sqrt_nonneg)
    ((energy_dual_integrable_referenceMeasure j).congr heq)
  rw [← integral_congr_ae heq] at h
  exact h

/-- The spin-weighted ordinary mass is finite, including the vanishing scalar spin term. -/
theorem spin_moment_cauchy (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) :
    Integrable (fun E => |(j : ℝ)| * ‖f E‖) (referenceMeasure j) ∧
      (∫ E, |(j : ℝ)| * ‖f E‖ ∂referenceMeasure j) ≤
        sqrt (∫ E, (j : ℝ) ^ 2 / (1 + E) ^ 4 ∂referenceMeasure j) *
          sqrt (∫ E, ‖f E‖ ^ 2 ∂energySpaceMeasure j) := by
  simpa only [sq_abs] using weighted_moment_cauchy j hf measurable_const
    (Filter.Eventually.of_forall (fun _ => abs_nonneg (j : ℝ)))
    (by simpa only [sq_abs] using spin_dual_integrable_referenceMeasure j)

/-- The ordinary square-integral expression is the actual weighted `L²` seminorm. -/
theorem energy_sqrt_integral_eq_eLpNorm (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) :
    sqrt (∫ E, ‖f E‖ ^ 2 ∂energySpaceMeasure j) =
      (eLpNorm f 2 (energySpaceMeasure j)).toReal := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← sqrt_eq_rpow, ENNReal.toReal_ofReal (sqrt_nonneg _)]

end GapFamily.Analytic
