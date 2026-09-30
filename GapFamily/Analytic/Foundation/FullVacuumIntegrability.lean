import GapFamily.Analytic.Foundation.FullVacuumRemainder
import GapFamily.Analytic.Kernel.HigherKernelResponseMoment

/-!
# Low-band integrability of the complete vacuum

The actual four-seed numerator is continuous and has an energy factor on every
physical low band. This establishes ordinary `L¹` and `L²` membership with
respect to the physical reference measure, including its scalar endpoint.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace GapFamily.Analytic

/-- The full vacuum numerator is continuous in real output energy. -/
theorem continuous_vacuumFullKernel (a : ℝ) (j : ℤ) :
    Continuous (fun e : ℝ => vacuumFullKernel a e j) := by
  have hc (J : ℤ) (E : ℂ) : Continuous (fun e : ℝ => fullKernelHol j J e E) := by
    have hp : Continuous (fun e : ℝ => ((e : ℂ), E)) :=
      Complex.continuous_ofReal.prodMk continuous_const
    simpa only [Function.comp_def] using (continuous_fullKernelHol j J).comp hp
  exact (((hc 0 (-a)).sub (hc 1 (1 - a))).sub (hc (-1) (1 - a))).add (hc 0 (2 - a))

/-- One energy-linear bound controls all physical spins in a fixed band. The
continued central term is absorbed using `|j| ≤ e`, even on the scalar row. -/
theorem exists_vacuumFullKernel_lowBand_bound (a B : ℝ) (ha : 2 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (e : ℝ),
      |(j : ℝ)| ≤ e → e ≤ B → ‖vacuumFullKernel a e j‖ ≤ C * e := by
  obtain ⟨C, hC, hcentral⟩ := exists_centralKernel_bound
  have ha0 : 0 ≤ a := by linarith
  refine ⟨2 * C + 64 * π ^ 2 * a * Real.exp (4 * π * Real.sqrt (a * B)),
    by positivity, ?_⟩
  intro j e he heB
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hc : ‖vacuumCentralKernel j‖ ≤ 2 * C * e :=
    (norm_vacuumCentralKernel_le C hcentral j).trans
      (mul_le_mul_of_nonneg_left he (by positivity))
  have hh : ‖vacuumHigherKernel a e j‖ ≤
      (64 * π ^ 2 * a * Real.exp (4 * π * Real.sqrt (a * B))) * e := by
    calc
      _ ≤ 64 * π ^ 2 * (a * e) * Real.exp (4 * π * Real.sqrt (a * e)) :=
        norm_vacuumHigherKernel_le a e j ha he
      _ ≤ 64 * π ^ 2 * (a * e) * Real.exp (4 * π * Real.sqrt (a * B)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left heB ha0)) (by positivity)
      _ = _ := by ring
  rw [vacuumFullKernel_eq_central_add_higher]
  exact (norm_add_le _ _).trans ((add_le_add hc hh).trans_eq (by ring))

/-- Ordinary absolute integrability of the actual full vacuum on each low band. -/
theorem vacuumFullKernel_lowBand_integrable (a B : ℝ) (j : ℤ) (ha : 2 ≤ a) :
    Integrable (fun e : ℝ => vacuumFullKernel a e j)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  obtain ⟨C, hC, hbound⟩ := exists_vacuumFullKernel_lowBand_bound a B ha
  apply ((lowBand_energy_integrable j B).const_mul C).mono'
    (continuous_vacuumFullKernel a j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact hbound j e he.1.le he.2.le

/-- The same actual numerator belongs to the Hilbert low band, including spin
zero where the unweighted reference measure has infinite mass. -/
theorem vacuumFullKernel_lowBand_memLp (a B : ℝ) (j : ℤ) (ha : 2 ≤ a) :
    MemLp (fun e : ℝ => vacuumFullKernel a e j) 2
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) := by
  by_cases hB : 0 ≤ B
  · obtain ⟨C, hC, hbound⟩ := exists_vacuumFullKernel_lowBand_bound a B ha
    apply ((lowBand_energy_memLp j B hB).const_mul C).mono'
      (continuous_vacuumFullKernel a j).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
    exact hbound j e he.1.le he.2.le
  · have hempty : Ioo |(j : ℝ)| B = ∅ :=
      Ioo_eq_empty_of_le ((le_of_not_ge hB).trans (abs_nonneg _))
    simp [hempty]

end GapFamily.Analytic
