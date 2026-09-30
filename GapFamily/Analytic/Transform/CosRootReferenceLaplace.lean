import GapFamily.Analytic.Transform.CosRootFixedDenominator
import GapFamily.Analytic.Foundation.ReferenceMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The fixed-denominator identity against the actual physical reference measure. -/
noncomputable section
namespace GapFamily.Analytic.CosRootLaplace
open Set MeasureTheory

/-- The intact source bracket with its genuine Laplace weight. -/
def fixedCosRootLaplace (c y E : ℝ) (j J : ℤ) (e : ℝ) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) * fixedCosRootBracket c E j J e

/-- The actual reference density gives precisely the ordinary convolution density. -/
theorem referenceDensity_mul_fixedCosRootLaplace (c y E : ℝ) (j J : ℤ) (e : ℝ) :
    (referenceDensity j e : ℂ) * fixedCosRootLaplace c y E j J e =
      fixedCosRootLaplaceDensity c y E j J e := by
  unfold referenceDensity fixedCosRootLaplace fixedCosRootLaplaceDensity
  push_cast
  ring

/-- Ordinary integrability under the actual physical reference measure is proved, not assumed. -/
theorem integrable_fixedCosRootLaplace {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    Integrable (fixedCosRootLaplace c y E j J) (referenceMeasure j) := by
  unfold referenceMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_referenceDensity j).ennreal_ofReal (by simp)]
  have h := integrableOn_fixedCosRootLaplaceDensity hc hy E j J
  apply h.congr
  filter_upwards with e
  rw [ENNReal.toReal_ofReal (referenceDensity_nonneg j e), Complex.real_smul,
    referenceDensity_mul_fixedCosRootLaplace]

/-- Exact ordinary change from the physical reference measure to its Lebesgue density. -/
theorem integral_fixedCosRootLaplace_reference (c y E : ℝ) (j J : ℤ) :
    (∫ e, fixedCosRootLaplace c y E j J e ∂referenceMeasure j) =
      ∫ e in Ioi |(j : ℝ)|, fixedCosRootLaplaceDensity c y E j J e := by
  unfold referenceMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_referenceDensity j).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards with e
  rw [ENNReal.toReal_ofReal (referenceDensity_nonneg j e), Complex.real_smul,
    referenceDensity_mul_fixedCosRootLaplace]

/-- The complete fixed-denominator source identity with its exact factor two and physical measure. -/
theorem integral_higherFourierKernel_eq_reference_laplace {c y : ℝ}
    (hc : 0 < c) (hy : 0 < y) (E : ℝ) (j J : ℤ) :
    (∫ t : ℝ, higherFourierKernel c y E j J t) =
      ((2 * Real.sqrt y / c : ℝ) : ℂ) *
        ∫ e, fixedCosRootLaplace c y E j J e ∂referenceMeasure j := by
  rw [integral_fixedCosRootLaplace_reference]
  exact integral_higherFourierKernel_eq_cosRoot_laplace hc hy E j J

/-- The actual Kloosterman-weighted higher-kernel summand has the same ordinary Laplace transform. -/
theorem integral_higherFourierKernel_eq_higherKernelTerm {y : ℝ} (hy : 0 < y)
    (E : ℝ) (j J : ℤ) (n : ℕ) :
    kloostermanSum j J n *
      (∫ t : ℝ, higherFourierKernel ((n + 1 : ℕ) : ℝ) y E j J t) =
      (Real.sqrt y : ℂ) * ∫ e,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          (2 * higherKernelTerm j J (e : ℂ) (E : ℂ) n) ∂referenceMeasure j := by
  have hc : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [integral_higherFourierKernel_eq_reference_laplace hc hy]
  have he : (fun e : ℝ => Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
      (2 * higherKernelTerm j J (e : ℂ) (E : ℂ) n)) =
      fun e => (2 * kloostermanSum j J n / ((n + 1 : ℕ) : ℂ)) *
        fixedCosRootLaplace ((n + 1 : ℕ) : ℝ) y E j J e := by
    funext e
    simp only [higherKernelTerm, fixedCosRootLaplace, fixedCosRootBracket,
      Complex.ofReal_natCast]
    ring
  rw [he, integral_const_mul]
  push_cast
  ring

/-- The actual nonzero-energy correction is the difference of two convergent physical Laplace integrals. -/
theorem integral_energyFourierKernel_eq_reference_laplace_difference {c y : ℝ}
    (hc : 0 < c) (hy : 0 < y) (E : ℝ) (j J : ℤ) :
    (∫ t : ℝ, PoincareEnergyFourier.energyFourierKernel
      c y (E : ℂ) j J (1 / 2 : ℂ) t) =
      ((2 * Real.sqrt y / c : ℝ) : ℂ) * ∫ e,
        (fixedCosRootLaplace c y E j J e - fixedCosRootLaplace c y 0 j J e)
          ∂referenceMeasure j := by
  have he : PoincareEnergyFourier.energyFourierKernel c y (E : ℂ) j J (1 / 2 : ℂ) =
      fun t => higherFourierKernel c y E j J t - higherFourierKernel c y 0 j J t := by
    funext t
    simp [higherFourierKernel, PoincareEnergyFourier.energyFourierKernel]
  rw [he, integral_sub (integrable_higherFourierKernel hc hy E j J)
    (integrable_higherFourierKernel hc hy 0 j J),
    integral_higherFourierKernel_eq_reference_laplace hc hy,
    integral_higherFourierKernel_eq_reference_laplace hc hy,
    integral_sub (integrable_fixedCosRootLaplace hc hy E j J)
      (integrable_fixedCosRootLaplace hc hy 0 j J), mul_sub]

end GapFamily.Analytic.CosRootLaplace
