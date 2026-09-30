import GapFamily.Analytic.Kernel.FullKernel
import GapFamily.Analytic.Kernel.HigherKernelThermalSpin
import GapFamily.Analytic.Poincare.Fourier.PoincareCentralLaplace

/-! Ordinary thermal integrability and complete spin summability of the full holomorphic kernel. -/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory

/-- The arithmetic spin factor is bounded by physical output energy. -/
theorem exists_thermal_centralKernel_bound (J : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℤ) (e t : ℝ), |(j : ℝ)| ≤ e →
      ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * centralKernel j J‖ ≤
        C * (e * Real.exp (-t * e)) := by
  obtain ⟨C, hC, hbound⟩ := exists_centralKernel_bound
  refine ⟨C * |(J : ℝ)|, by positivity, ?_⟩
  intro j e t he
  rw [norm_mul, norm_exp_thermal]
  calc
    _ ≤ Real.exp (-t * e) * (C * (|(j : ℝ)| * |(J : ℝ)|)) :=
      mul_le_mul_of_nonneg_left (hbound j J) (Real.exp_pos _).le
    _ ≤ Real.exp (-t * e) * (C * (e * |(J : ℝ)|)) := by gcongr
    _ = _ := by ring

/-- The constant central numerator is thermally integrable in every spin,
including the scalar channel where it vanishes. -/
theorem integrable_thermal_centralKernel (j J : ℤ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun e : ℝ => Complex.exp (-(t : ℂ) * (e : ℂ)) * centralKernel j J)
      (referenceMeasure j) := by
  obtain ⟨C, _, hC⟩ := exists_thermal_centralKernel_bound J
  apply ((integrable_energy_exp_referenceMeasure j ht).const_mul C).mono'
  · exact ((Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).mul continuous_const).aestronglyMeasurable
  · filter_upwards [referenceMeasure_ae_above_edge j] with e he
    exact hC j e t he.le

/-- The central thermal integral is absolutely summable over all output spins. -/
theorem summable_integral_norm_thermal_centralKernel_spin (J : ℤ)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ e : ℝ,
      ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * centralKernel j J‖ ∂referenceMeasure j) := by
  obtain ⟨C, _, hC⟩ := exists_thermal_centralKernel_bound J
  apply ((summable_integral_energy_exp_referenceMeasure ht).mul_left C).of_nonneg_of_le
  · exact fun j => integral_nonneg fun _ => norm_nonneg _
  · intro j
    calc
      _ ≤ ∫ e, C * (e * Real.exp (-t * e)) ∂referenceMeasure j := by
        apply integral_mono_ae (integrable_thermal_centralKernel j J ht).norm
          ((integrable_energy_exp_referenceMeasure j ht).const_mul C)
        filter_upwards [referenceMeasure_ae_above_edge j] with e he
        exact hC j e t he.le
      _ = _ := integral_const_mul _ _

/-- The full holomorphic kernel has an ordinary absolutely convergent thermal transform. -/
theorem integrable_thermal_fullKernelHol (j J : ℤ) (E : ℂ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun e : ℝ => Complex.exp (-(t : ℂ) * (e : ℂ)) * fullKernelHol j J e E)
      (referenceMeasure j) := by
  convert (integrable_thermal_centralKernel j J ht).add
    (integrable_thermal_higherKernel j J E ht) using 1
  ext e
  simp only [fullKernelHol, mul_add, Pi.add_apply]

/-- The full ordinary thermal output is absolutely summable over every integer spin. -/
theorem summable_integral_norm_thermal_fullKernelHol_spin (J : ℤ) (E : ℂ)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ e : ℝ,
      ‖Complex.exp (-(t : ℂ) * (e : ℂ)) * fullKernelHol j J e E‖ ∂referenceMeasure j) := by
  apply ((summable_integral_norm_thermal_centralKernel_spin J ht).add
    (summable_integral_norm_thermal_higherKernel_spin J E ht)).of_nonneg_of_le
  · exact fun j => integral_nonneg fun _ => norm_nonneg _
  · intro j
    rw [← integral_add (integrable_thermal_centralKernel j J ht).norm
      (integrable_thermal_higherKernel j J E ht).norm]
    apply integral_mono_ae (integrable_thermal_fullKernelHol j J E ht).norm
      ((integrable_thermal_centralKernel j J ht).norm.add
        (integrable_thermal_higherKernel j J E ht).norm)
    exact Filter.Eventually.of_forall fun e => by
      simpa only [fullKernelHol, mul_add, Pi.add_apply] using
        norm_add_le (Complex.exp (-(t : ℂ) * (e : ℂ)) * centralKernel j J)
          (Complex.exp (-(t : ℂ) * (e : ℂ)) * higherKernel j J e E)

end GapFamily.Analytic
