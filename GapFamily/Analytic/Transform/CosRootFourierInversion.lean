import GapFamily.Analytic.Transform.CosRootHigherFourier
import GapFamily.Analytic.Transform.CosRootFourierProduct

/-! Actual fixed-denominator Fourier inversion, before changing to the output energy coordinate. -/
noncomputable section
namespace GapFamily.Analytic.CosRootLaplace
open Set MeasureTheory
open scoped FourierTransform

/-- The exact physical regularized convolution, with both input combinations retained. -/
def physicalCosRootConvolution (c y E : ℝ) (J : ℤ) : ℝ → ℂ :=
  cosRootConvolution (2 * Real.pi * y)
    ((8 * Real.pi ^ 2 * (E + (J : ℝ)) / c ^ 2 : ℝ) : ℂ)
    ((8 * Real.pi ^ 2 * (E - (J : ℝ)) / c ^ 2 : ℝ) : ℂ)

/-- The Fourier transform of the actual physical convolution is the complete higher bracket. -/
theorem fourier_physicalCosRootConvolution {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E : ℝ) (J : ℤ) (t : ℝ) :
    𝓕 (physicalCosRootConvolution c y E J) t =
      ((1 / (2 * Real.sqrt (t ^ 2 + y ^ 2)) : ℝ) : ℂ) *
        (Complex.exp (-2 * (Real.pi : ℂ) *
          (((E * y : ℝ) : ℂ) + (((J : ℝ) * t : ℝ) : ℂ) * Complex.I) /
            ((c ^ 2 * (t ^ 2 + y ^ 2) : ℝ) : ℂ)) - 1) := by
  unfold physicalCosRootConvolution
  rw [fourier_cosRootConvolution (by positivity)]
  rw [halfFourierValue_physical_product hc hy]
  have hz := halfFourierValue_physical_product hc hy 0 0 t
  simp only [zero_sub, mul_zero, zero_div, neg_zero, zero_mul, add_zero,
    Complex.exp_zero, mul_one, Complex.ofReal_zero] at hz
  rw [hz]
  ring

/-- Exact normalization against the original higher unrolled kernel, including the output phase. -/
theorem higherFourierKernel_eq_fourier {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) (t : ℝ) :
    higherFourierKernel c y E j J t =
      ((2 * Real.sqrt y / c : ℝ) : ℂ) *
        (cuspFourierMode (-j) t * 𝓕 (physicalCosRootConvolution c y E J) t) := by
  rw [higherFourierKernel_eq_exp hc hy, fourier_physicalCosRootConvolution hc hy]
  push_cast
  ring

/-- Actual Fourier integrability follows from the proved energy and phase remainders. -/
theorem integrable_fourier_physicalCosRootConvolution {c y : ℝ}
    (hc : 0 < c) (hy : 0 < y) (E : ℝ) (J : ℤ) :
    Integrable (𝓕 (physicalCosRootConvolution c y E J)) := by
  have hscale : ((2 * Real.sqrt y / c : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have he : 𝓕 (physicalCosRootConvolution c y E J) =
      fun t => ((2 * Real.sqrt y / c : ℝ) : ℂ)⁻¹ * higherFourierKernel c y E 0 J t := by
    funext t
    rw [higherFourierKernel_eq_fourier hc hy]
    have hphase : cuspFourierMode (-(0 : ℤ)) t = 1 := by simp [cuspFourierMode]
    rw [hphase, one_mul, ← mul_assoc, inv_mul_cancel₀ hscale, one_mul]
  rw [he]
  exact (integrable_higherFourierKernel hc hy E 0 J).const_mul _

/-- The actual higher Fourier coefficient is an ordinary convolution value, also for output spin zero. -/
theorem integral_higherFourierKernel_eq_convolution {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    (∫ t : ℝ, higherFourierKernel c y E j J t) =
      ((2 * Real.sqrt y / c : ℝ) : ℂ) *
        physicalCosRootConvolution c y E J (-(j : ℝ)) := by
  have ha : 0 < 2 * Real.pi * y := by positivity
  have hf : Integrable (physicalCosRootConvolution c y E J) :=
    integrable_cosRootConvolution ha _ _
  have hcont : Continuous (physicalCosRootConvolution c y E J) :=
    continuous_cosRootConvolution ha _ _
  have hinv := hf.fourierInv_fourier_eq
    (integrable_fourier_physicalCosRootConvolution hc hy E J)
    (hcont.continuousAt (x := -(j : ℝ)))
  rw [Real.fourierInv_eq_fourier_neg, neg_neg,
    Real.fourier_real_eq_integral_exp_smul] at hinv
  simp_rw [higherFourierKernel_eq_fourier hc hy E j J]
  rw [integral_const_mul]
  congr 1
  convert hinv using 1
  congr 1
  funext t
  rw [smul_eq_mul]
  congr 1
  unfold cuspFourierMode
  congr 1
  push_cast
  ring

end GapFamily.Analytic.CosRootLaplace
