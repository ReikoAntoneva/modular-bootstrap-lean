import GapFamily.Analytic.Transform.CosRootFourierInversion
import GapFamily.Analytic.Transform.CosRootConvolutionCoordinate
import GapFamily.Analytic.Arithmetic.Kloosterman

/-! The actual source cosRoot bracket is the ordinary inverse transform at each positive denominator. -/
noncomputable section
namespace GapFamily.Analytic.CosRootLaplace
open Set MeasureTheory

/-- The intact fixed-denominator bracket from the actual higher kernel. -/
def fixedCosRootBracket (c E : ℝ) (j J : ℤ) (e : ℝ) : ℂ :=
  cosRoot (higherKernelArgPlus j J (e : ℂ) (E : ℂ) / (c : ℂ) ^ 2) *
    cosRoot (higherKernelArgMinus j J (e : ℂ) (E : ℂ) / (c : ℂ) ^ 2) - 1

/-- The ordinary density against Lebesgue measure, on the strict physical half-line. -/
def fixedCosRootLaplaceDensity (c y E : ℝ) (j J : ℤ) (e : ℝ) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) /
    (Real.sqrt (e ^ 2 - (j : ℝ) ^ 2) : ℂ) * fixedCosRootBracket c E j J e

/-- Exact conversion of the half-profile parameters to the source's two factors of four pi squared. -/
theorem physicalCosRootConvolution_energyKernel (c y E : ℝ) (j J : ℤ) (e : ℝ) :
    cosRootConvolutionEnergyKernel (2 * Real.pi * y)
      ((8 * Real.pi ^ 2 * (E + (J : ℝ)) / c ^ 2 : ℝ) : ℂ)
      ((8 * Real.pi ^ 2 * (E - (J : ℝ)) / c ^ 2 : ℝ) : ℂ) (j : ℝ) e =
      fixedCosRootLaplaceDensity c y E j J e := by
  unfold cosRootConvolutionEnergyKernel fixedCosRootLaplaceDensity fixedCosRootBracket
    higherKernelArgPlus higherKernelArgMinus
  push_cast
  congr 2 <;> ring_nf

/-- Ordinary integrability is derived from the actual regularized convolution, including output zero. -/
theorem integrableOn_fixedCosRootLaplaceDensity {c y : ℝ} (_hc : 0 < c) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    IntegrableOn (fixedCosRootLaplaceDensity c y E j J) (Ioi |(j : ℝ)|) := by
  have h := integrableOn_cosRootConvolutionEnergyKernel
    (show 0 < 2 * Real.pi * y by positivity)
    (((8 * Real.pi ^ 2 * (E + (J : ℝ)) / c ^ 2 : ℝ) : ℂ))
    (((8 * Real.pi ^ 2 * (E - (J : ℝ)) / c ^ 2 : ℝ) : ℂ)) (j : ℝ)
  exact h.congr (Filter.Eventually.of_forall (physicalCosRootConvolution_energyKernel c y E j J))

/-- The actual higher fixed-denominator Fourier coefficient is the literal ordinary source integral. -/
theorem integral_higherFourierKernel_eq_cosRoot_laplace {c y : ℝ}
    (hc : 0 < c) (hy : 0 < y) (E : ℝ) (j J : ℤ) :
    (∫ t : ℝ, higherFourierKernel c y E j J t) =
      ((2 * Real.sqrt y / c : ℝ) : ℂ) *
        ∫ e in Ioi |(j : ℝ)|, fixedCosRootLaplaceDensity c y E j J e := by
  rw [integral_higherFourierKernel_eq_convolution hc hy]
  unfold physicalCosRootConvolution
  rw [cosRootConvolution_eq_energy_integral (show 0 < 2 * Real.pi * y by positivity)]
  simp only [physicalCosRootConvolution_energyKernel]

end GapFamily.Analytic.CosRootLaplace
