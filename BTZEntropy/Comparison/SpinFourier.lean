import GapFamily.Analytic.Transform.CosRootReferenceLaplace
import GapFamily.Analytic.Foundation.Vacuum

/-!
# Fourier coefficient of the vacuum image

The four vacuum seeds are combined before integrating. Each coefficient is the
ordinary thermal transform of the actual denominator-one vacuum numerator
against the physical reference measure, including the scalar spin.
-/

noncomputable section

open MeasureTheory
open GapFamily.Analytic GapFamily.Analytic.CosRootLaplace

namespace BTZEntropy

/-- The denominator-one modular image, with all four vacuum seeds retained. -/
def spinImageKernel (a y t : ℝ) : ℂ :=
  higherFourierKernel 1 y (-a) 0 0 t -
    higherFourierKernel 1 y (1 - a) 0 1 t -
    higherFourierKernel 1 y (1 - a) 0 (-1) t +
    higherFourierKernel 1 y (2 - a) 0 0 t

private theorem exp_four_term (q z u v : ℂ) :
    q * (Complex.exp z - 1) - q * (Complex.exp (z + u) - 1) -
      q * (Complex.exp (z + v) - 1) + q * (Complex.exp (z + u + v) - 1) =
      q * Complex.exp z * (1 - Complex.exp u) * (1 - Complex.exp v) := by
  simp only [Complex.exp_add]
  ring

/-- The literal modular image has the two vacuum null factors. -/
theorem spinImageKernel_eq_exp {y : ℝ} (hy : 0 < y) (a t : ℝ) :
    spinImageKernel a y t =
      ((Real.sqrt y / Real.sqrt (t ^ 2 + y ^ 2) : ℝ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * (a : ℂ) * (y : ℂ) /
          ((t ^ 2 + y ^ 2 : ℝ) : ℂ)) *
        (1 - Complex.exp (-2 * (Real.pi : ℂ) * ((y : ℂ) + (t : ℂ) * Complex.I) /
          ((t ^ 2 + y ^ 2 : ℝ) : ℂ))) *
        (1 - Complex.exp (-2 * (Real.pi : ℂ) * ((y : ℂ) - (t : ℂ) * Complex.I) /
          ((t ^ 2 + y ^ 2 : ℝ) : ℂ))) := by
  unfold spinImageKernel
  simp only [higherFourierKernel_eq_exp (show (0 : ℝ) < 1 by norm_num) hy]
  convert exp_four_term
    (((Real.sqrt y / Real.sqrt (t ^ 2 + y ^ 2) : ℝ) : ℂ))
    (2 * (Real.pi : ℂ) * (a : ℂ) * (y : ℂ) / ((t ^ 2 + y ^ 2 : ℝ) : ℂ))
    (-2 * (Real.pi : ℂ) * ((y : ℂ) + (t : ℂ) * Complex.I) /
      ((t ^ 2 + y ^ 2 : ℝ) : ℂ))
    (-2 * (Real.pi : ℂ) * ((y : ℂ) - (t : ℂ) * Complex.I) /
      ((t ^ 2 + y ^ 2 : ℝ) : ℂ)) using 1 <;>
    push_cast <;> norm_num <;> congr 2 <;> ring

theorem spinImageKernel_zero {y : ℝ} (hy : 0 < y) (a : ℝ) :
    spinImageKernel a y 0 =
      ((Real.sqrt y / y * Real.exp (2 * Real.pi * a / y) *
        (1 - Real.exp (-2 * Real.pi / y)) ^ 2 : ℝ) : ℂ) := by
  rw [spinImageKernel_eq_exp hy]
  have hne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
  have harg : 2 * (Real.pi : ℂ) * (a : ℂ) * (y : ℂ) / (y : ℂ) ^ 2 =
      2 * (Real.pi : ℂ) * (a : ℂ) / (y : ℂ) := by field_simp
  have hnull : -2 * (Real.pi : ℂ) * (y : ℂ) / (y : ℂ) ^ 2 =
      -2 * (Real.pi : ℂ) / (y : ℂ) := by field_simp
  push_cast
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, zero_mul, add_zero,
    sub_zero, Real.sqrt_sq hy.le, harg, hnull]
  ring

theorem higherFourierKernel_eq_mode {y : ℝ} (hy : 0 < y)
    (E : ℝ) (j J : ℤ) (t : ℝ) :
    higherFourierKernel 1 y E j J t =
      cuspFourierMode (-j) t * higherFourierKernel 1 y E 0 J t := by
  rw [higherFourierKernel_eq_exp (by norm_num) hy,
    higherFourierKernel_eq_exp (by norm_num) hy]
  simp only [neg_zero, cuspFourierMode_zero, mul_one]
  ring

theorem higherFourierKernel_fourSeed_eq_mode {y : ℝ} (hy : 0 < y)
    (a : ℝ) (j : ℤ) (t : ℝ) :
    higherFourierKernel 1 y (-a) j 0 t -
      higherFourierKernel 1 y (1 - a) j 1 t -
      higherFourierKernel 1 y (1 - a) j (-1) t +
      higherFourierKernel 1 y (2 - a) j 0 t =
        cuspFourierMode (-j) t * spinImageKernel a y t := by
  rw [higherFourierKernel_eq_mode hy (-a) j 0,
    higherFourierKernel_eq_mode hy (1 - a) j 1,
    higherFourierKernel_eq_mode hy (1 - a) j (-1),
    higherFourierKernel_eq_mode hy (2 - a) j 0]
  unfold spinImageKernel
  ring

theorem integrable_spinImageKernel {y : ℝ} (hy : 0 < y) (a : ℝ) :
    Integrable (spinImageKernel a y) :=
  (((integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (-a) 0 0).sub
    (integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (1 - a) 0 1)).sub
    (integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (1 - a) 0 (-1))).add
    (integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (2 - a) 0 0)

theorem continuous_spinImageKernel {y : ℝ} (hy : 0 < y) (a : ℝ) :
    Continuous (spinImageKernel a y) := by
  have hc (E : ℝ) (J : ℤ) : Continuous (higherFourierKernel 1 y E 0 J) :=
    (PoincareEnergyFourier.continuous_energyFourierKernel (by norm_num) hy E 0 J _).add
      (PoincareFourierRemainder.continuous_fourierRemainderKernel (by norm_num) hy 0 J _)
  exact (((hc (-a) 0).sub (hc (1 - a) 1)).sub (hc (1 - a) (-1))).add (hc (2 - a) 0)

theorem integrable_mode_mul_spinImageKernel {y : ℝ} (hy : 0 < y) (a : ℝ) (j : ℤ) :
    Integrable (fun t => cuspFourierMode (-j) t * spinImageKernel a y t) := by
  have h := (((integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (-a) j 0).sub
    (integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (1 - a) j 1)).sub
    (integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (1 - a) j (-1))).add
    (integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (2 - a) j 0)
  exact h.congr (Filter.Eventually.of_forall (higherFourierKernel_fourSeed_eq_mode hy a j))

private theorem integrable_seedThermal {y : ℝ} (hy : 0 < y) (E : ℝ) (j J : ℤ) :
    Integrable (fun e : ℝ =>
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        (2 * higherKernelTerm j J (e : ℂ) (E : ℂ) 0)) (referenceMeasure j) := by
  apply ((integrable_fixedCosRootLaplace (by norm_num : (0 : ℝ) < 1)
    hy E j J).const_mul (2 : ℂ)).congr
  apply Filter.Eventually.of_forall
  intro e
  simp only [higherKernelTerm_zero, fixedCosRootLaplace, fixedCosRootBracket,
    Complex.ofReal_one, one_pow, div_one]
  ring

private theorem integral_four {μ : Measure ℝ} {f g h k : ℝ → ℂ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) (hk : Integrable k μ) :
    (∫ t, (f t - g t - h t + k t) ∂μ) =
      (∫ t, f t ∂μ) - (∫ t, g t ∂μ) - (∫ t, h t ∂μ) + ∫ t, k t ∂μ := by
  have h1 := integral_add ((hf.sub hg).sub hh) hk
  have h2 := integral_sub (hf.sub hg) hh
  have h3 := integral_sub hf hg
  simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 h3
  rw [h1, h2, h3]

theorem integral_mode_mul_spinImageKernel_eq_fourSeed {y : ℝ}
    (hy : 0 < y) (a : ℝ) (j : ℤ) :
    (∫ t : ℝ, cuspFourierMode (-j) t * spinImageKernel a y t) =
      (∫ t : ℝ, higherFourierKernel 1 y (-a) j 0 t) -
        (∫ t : ℝ, higherFourierKernel 1 y (1 - a) j 1 t) -
        (∫ t : ℝ, higherFourierKernel 1 y (1 - a) j (-1) t) +
        ∫ t : ℝ, higherFourierKernel 1 y (2 - a) j 0 t := by
  rw [show (fun t => cuspFourierMode (-j) t * spinImageKernel a y t) =
      (fun t => higherFourierKernel 1 y (-a) j 0 t -
        higherFourierKernel 1 y (1 - a) j 1 t -
        higherFourierKernel 1 y (1 - a) j (-1) t +
        higherFourierKernel 1 y (2 - a) j 0 t) from
      funext (fun t => (higherFourierKernel_fourSeed_eq_mode hy a j t).symm)]
  exact integral_four
    (integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (-a) j 0)
    (integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (1 - a) j 1)
    (integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (1 - a) j (-1))
    (integrable_higherFourierKernel (by norm_num : (0 : ℝ) < 1) hy (2 - a) j 0)

theorem integrable_vacuumLeadingThermal {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) (j : ℤ) :
    Integrable (fun e : ℝ =>
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        (vacuumLeading a e j : ℂ)) (referenceMeasure j) := by
  have h := (((integrable_seedThermal hy (-a) j 0).sub
    (integrable_seedThermal hy (1 - a) j 1)).sub
    (integrable_seedThermal hy (1 - a) j (-1))).add
    (integrable_seedThermal hy (2 - a) j 0)
  apply h.congr
  filter_upwards [referenceMeasure_ae_above_edge j] with e he
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [← vacuumHigherTerm_zero_eq_ofReal a e j ha he.le]
  simp only [vacuumHigherTerm, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring

theorem integral_mode_mul_spinImageKernel_eq {a y : ℝ}
    (ha : 2 ≤ a) (hy : 0 < y) (j : ℤ) :
    (∫ t : ℝ, cuspFourierMode (-j) t * spinImageKernel a y t) =
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          (vacuumLeading a e j : ℂ) ∂referenceMeasure j := by
  have hk (E : ℝ) (J : ℤ) :
      (∫ t : ℝ, higherFourierKernel 1 y E j J t) =
        (Real.sqrt y : ℂ) * ∫ e : ℝ,
          Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
            (2 * higherKernelTerm j J (e : ℂ) (E : ℂ) 0) ∂referenceMeasure j := by
    simpa only [Nat.zero_add, Nat.cast_one, kloostermanSum_zero, one_mul] using
      integral_higherFourierKernel_eq_higherKernelTerm hy E j J 0
  rw [integral_mode_mul_spinImageKernel_eq_fourSeed hy]
  simp only [hk, ← mul_sub, ← mul_add]
  congr 1
  rw [← integral_four (integrable_seedThermal hy (-a) j 0)
    (integrable_seedThermal hy (1 - a) j 1)
    (integrable_seedThermal hy (1 - a) j (-1))
    (integrable_seedThermal hy (2 - a) j 0)]
  apply integral_congr_ae
  filter_upwards [referenceMeasure_ae_above_edge j] with e he
  rw [← vacuumHigherTerm_zero_eq_ofReal a e j ha he.le]
  simp only [vacuumHigherTerm, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring

end BTZEntropy
