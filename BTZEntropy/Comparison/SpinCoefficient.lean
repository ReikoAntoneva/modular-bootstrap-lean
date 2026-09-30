import BTZEntropy.Comparison.SpinFourier
import GapFamily.Analytic.Kernel.HigherKernelThermalSpin

/-!
# Absolute summability of the vacuum image coefficient

The physical thermal envelope bounds each denominator-one seed before the
integer-spin sum. This supplies the actual summable Fourier coefficients needed
for Poisson summation of the vacuum image.
-/

noncomputable section

open MeasureTheory
open GapFamily.Analytic GapFamily.Analytic.CosRootLaplace
open scoped FourierTransform

namespace BTZEntropy

theorem summable_integral_norm_thermal_higherKernelTerm_zero_spin
    (J : ℤ) (E : ℂ) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ e : ℝ,
      ‖Complex.exp (-(t : ℂ) * (e : ℂ)) *
        (2 * higherKernelTerm j J e E 0)‖ ∂referenceMeasure j) := by
  have hs := (summable_integral_energy_exp_sqrt_referenceMeasure
    (8 * Real.pi * Real.sqrt (‖E‖ + |(J : ℝ)|)) ht).mul_left
      (8 * Real.pi ^ 2 * (‖E‖ + |(J : ℝ)|))
  apply hs.of_nonneg_of_le
  · intro j
    exact integral_nonneg fun _ => norm_nonneg _
  · intro j
    calc
      _ ≤ ∫ e, higherKernelThermalEnvelope J E t e ∂referenceMeasure j := by
        apply integral_mono_ae (integrable_thermal_higherKernelTerm j J E ht 0).norm
          (integrable_higherKernelThermalEnvelope j J E ht)
        filter_upwards [referenceMeasure_ae_above_edge j] with e he
        simpa only [Nat.cast_zero, zero_add, one_pow, div_one, mul_one,
          higherKernelThermalEnvelope] using norm_thermal_higherKernelTerm_le j J e E t he.le 0
      _ = _ := by simp only [higherKernelThermalEnvelope, integral_const_mul]

theorem summable_integral_thermal_higherKernelTerm_zero_spin
    (J : ℤ) (E : ℂ) {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => ∫ e : ℝ,
      Complex.exp (-(t : ℂ) * (e : ℂ)) *
        (2 * higherKernelTerm j J e E 0) ∂referenceMeasure j) :=
  (summable_integral_norm_thermal_higherKernelTerm_zero_spin J E ht).of_norm_bounded
    (fun _ => norm_integral_le_integral_norm _)

theorem summable_integral_higherFourierKernel_one {y : ℝ} (hy : 0 < y)
    (E : ℝ) (J : ℤ) :
    Summable (fun j : ℤ => ∫ t : ℝ, higherFourierKernel 1 y E j J t) := by
  have hs := (summable_integral_thermal_higherKernelTerm_zero_spin J (E : ℂ)
    (show 0 < 2 * Real.pi * y by positivity)).mul_left (Real.sqrt y : ℂ)
  apply hs.congr
  intro j
  have h := integral_higherFourierKernel_eq_higherKernelTerm hy E j J 0
  simp only [Nat.zero_add, Nat.cast_one, kloostermanSum_zero, one_mul] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro e
  push_cast
  ring_nf

theorem summable_integral_mode_mul_spinImageKernel {y : ℝ} (hy : 0 < y) (a : ℝ) :
    Summable (fun j : ℤ => ∫ t : ℝ,
      cuspFourierMode (-j) t * spinImageKernel a y t) := by
  have hs := (((summable_integral_higherFourierKernel_one hy (-a) 0).sub
    (summable_integral_higherFourierKernel_one hy (1 - a) 1)).sub
    (summable_integral_higherFourierKernel_one hy (1 - a) (-1))).add
    (summable_integral_higherFourierKernel_one hy (2 - a) 0)
  exact hs.congr fun j => (integral_mode_mul_spinImageKernel_eq_fourSeed hy a j).symm

theorem fourier_spinImageKernel_eq (a y : ℝ) (j : ℤ) :
    𝓕 (spinImageKernel a y) (j : ℝ) =
      ∫ t : ℝ, cuspFourierMode (-j) t * spinImageKernel a y t := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [smul_eq_mul, cuspFourierMode, RCLike.inner_apply, conj_trivial]
  congr 2
  push_cast
  ring

theorem summable_fourier_spinImageKernel {y : ℝ} (hy : 0 < y) (a : ℝ) :
    Summable (fun j : ℤ => 𝓕 (spinImageKernel a y) (j : ℝ)) := by
  simpa only [fourier_spinImageKernel_eq] using
    summable_integral_mode_mul_spinImageKernel hy a

theorem fourier_spinImageKernel_eq_reference {a y : ℝ}
    (ha : 2 ≤ a) (hy : 0 < y) (j : ℤ) :
    𝓕 (spinImageKernel a y) (j : ℝ) =
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          (vacuumLeading a e j : ℂ) ∂referenceMeasure j := by
  rw [fourier_spinImageKernel_eq, integral_mode_mul_spinImageKernel_eq ha hy]

end BTZEntropy
