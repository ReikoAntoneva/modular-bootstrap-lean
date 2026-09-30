import GapFamily.Analytic.Transform.CosRootConvolution
import GapFamily.Analytic.Poincare.Fourier.PoincareEnergyFourierKernel
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRemainderBound

/-! The actual higher fixed-denominator Fourier kernel, including its energy correction. -/
noncomputable section
namespace GapFamily.Analytic.CosRootLaplace
open Set MeasureTheory
open scoped FourierTransform
open PoincareEnergyFourier PoincareFourierRemainder

/-- The complete higher bracket is formed before integration, retaining the scalar cancellation. -/
def higherFourierKernel (c y E : ℝ) (j J : ℤ) (t : ℝ) : ℂ :=
  energyFourierKernel c y (E : ℂ) j J (1 / 2 : ℂ) t +
    fourierRemainderKernel c y j J (1 / 2 : ℂ) t

/-- The actual higher bracket is ordinarily integrable for all input and output spins. -/
theorem integrable_higherFourierKernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) : Integrable (higherFourierKernel c y E j J) := by
  exact (integrable_energyFourierKernel hc hy (E : ℂ) j J (by norm_num)).add
    (integrable_fourierRemainderKernel hc hy j J (by norm_num))

private theorem height_cpow_half {c y : ℝ} (hc : 0 < c) (hy : 0 < y) (t : ℝ) :
    ((y / (c ^ 2 * (t ^ 2 + y ^ 2)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((Real.sqrt y / (c * Real.sqrt (t ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
  have hp : 0 ≤ y / (c ^ 2 * (t ^ 2 + y ^ 2)) := by positivity
  calc
    _ = ((Real.sqrt (y / (c ^ 2 * (t ^ 2 + y ^ 2))) : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow]
      simpa using (Complex.ofReal_cpow hp (1 / 2 : ℝ)).symm
    _ = _ := by
      rw [Real.sqrt_div hy.le, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]

/-- The signs and factors of the literal higher Fourier bracket. -/
theorem higherFourierKernel_eq_exp {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) (t : ℝ) :
    higherFourierKernel c y E j J t =
      ((Real.sqrt y / (c * Real.sqrt (t ^ 2 + y ^ 2)) : ℝ) : ℂ) *
        cuspFourierMode (-j) t *
        (Complex.exp (-2 * (Real.pi : ℂ) *
          (((E * y : ℝ) : ℂ) + (((J : ℝ) * t : ℝ) : ℂ) * Complex.I) /
            ((c ^ 2 * (t ^ 2 + y ^ 2) : ℝ) : ℂ)) - 1) := by
  have hd : ((c ^ 2 * (t ^ 2 + y ^ 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have he : cuspFourierMode (-J) (t / (c ^ 2 * (t ^ 2 + y ^ 2))) *
      Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) *
        ((y / (c ^ 2 * (t ^ 2 + y ^ 2)) : ℝ) : ℂ)) =
      Complex.exp (-2 * (Real.pi : ℂ) *
        (((E * y : ℝ) : ℂ) + (((J : ℝ) * t : ℝ) : ℂ) * Complex.I) /
          ((c ^ 2 * (t ^ 2 + y ^ 2) : ℝ) : ℂ)) := by
    unfold cuspFourierMode
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold higherFourierKernel energyFourierKernel fourierRemainderKernel
    PoincareFourierUnfold.fourierKernel
  rw [height_cpow_half hc hy]
  calc
    _ = ((Real.sqrt y / (c * Real.sqrt (t ^ 2 + y ^ 2)) : ℝ) : ℂ) *
        cuspFourierMode (-j) t *
        (cuspFourierMode (-J) (t / (c ^ 2 * (t ^ 2 + y ^ 2))) *
          Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) *
            ((y / (c ^ 2 * (t ^ 2 + y ^ 2)) : ℝ) : ℂ)) - 1) := by ring
    _ = _ := by rw [he]

end GapFamily.Analytic.CosRootLaplace
