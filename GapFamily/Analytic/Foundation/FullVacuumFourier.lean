import GapFamily.Analytic.Foundation.FullVacuumReality
import GapFamily.Analytic.Poincare.Fourier.PoincareFullFourierLaplace
import GapFamily.Analytic.Poincare.Seed.PoincareGeneralSeedSmooth

/-!
# The actual modular vacuum and its complete Fourier output

The function is the four signed canonical threshold seeds. The output identity
retains their direct inputs, the scalar atom of weight minus six, and the
ordinary continuum against the open physical reference measure.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory UpperHalfPlane CuspFourierCutoff
open PoincareEnergyContinuation PoincareEnergyFourier PoincareScalarFourier
open PoincareFourier
open scoped ContDiff MatrixGroups

/-- The canonical modular completion of the vacuum and its two null subtractions. -/
def vacuumReducedSeed (a : ℝ) (τ : UpperHalfPlane) : ℂ :=
  generalThresholdSeed (-a) 0 τ - generalThresholdSeed (1 - a) 1 τ -
    generalThresholdSeed (1 - a) (-1) τ + generalThresholdSeed (2 - a) 0 τ

theorem continuous_vacuumReducedSeed (a : ℝ) : Continuous (vacuumReducedSeed a) :=
  (((continuous_generalThresholdSeed (-a) 0).sub
    (continuous_generalThresholdSeed (1 - a) 1)).sub
    (continuous_generalThresholdSeed (1 - a) (-1))).add
    (continuous_generalThresholdSeed (2 - a) 0)

/-- The four-seed completion is modular at the actual threshold parameter. -/
theorem vacuumReducedSeed_smul (a : ℝ) (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    vacuumReducedSeed a (g • τ) = vacuumReducedSeed a τ := by
  simp only [vacuumReducedSeed, generalThresholdSeed_smul]

/-- The actual vacuum completion is smooth at every upper-half-plane point. -/
theorem contDiffAt_vacuumReducedSeed (a : ℝ) (τ : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (fun z : ℂ => vacuumReducedSeed a (ofComplex z)) (τ : ℂ) :=
  (((contDiffAt_generalThresholdSeed (-a) 0 τ).sub
    (contDiffAt_generalThresholdSeed (1 - a) 1 τ)).sub
    (contDiffAt_generalThresholdSeed (1 - a) (-1) τ)).add
    (contDiffAt_generalThresholdSeed (2 - a) 0 τ)

/-- An ordinary horizontal Fourier coefficient of the actual modular function. -/
def vacuumFourierCoefficient (a y : ℝ) (hy : 0 < y) (j : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x * vacuumReducedSeed a (rowPoint y hy x)

theorem vacuumFourierCoefficient_eq_four_seed (a y : ℝ) (hy : 0 < y) (j : ℤ) :
    vacuumFourierCoefficient a y hy j =
      generalThresholdFourierCoefficient y hy (-a) j 0 -
        generalThresholdFourierCoefficient y hy (1 - a) j 1 -
        generalThresholdFourierCoefficient y hy (1 - a) j (-1) +
        generalThresholdFourierCoefficient y hy (2 - a) j 0 := by
  have h0 := intervalIntegrable_generalThresholdFourierIntegrand y hy (-a) j 0
  have hp := intervalIntegrable_generalThresholdFourierIntegrand y hy (1 - a) j 1
  have hm := intervalIntegrable_generalThresholdFourierIntegrand y hy (1 - a) j (-1)
  have h2 := intervalIntegrable_generalThresholdFourierIntegrand y hy (2 - a) j 0
  simp only [vacuumFourierCoefficient, vacuumReducedSeed, mul_add, mul_sub]
  rw [intervalIntegral.integral_add ((h0.sub hp).sub hm) h2,
    intervalIntegral.integral_sub (h0.sub hp) hm, intervalIntegral.integral_sub h0 hp]
  rfl

/-- The four prescribed signed direct inputs, before adding any induced output. -/
def vacuumDirectFourier (a y : ℝ) (j : ℤ) : ℂ :=
  (if j = 0 then (Real.sqrt y : ℂ) *
    Complex.exp (-2 * (Real.pi : ℂ) * (-a) * (y : ℂ)) else 0) -
  (if j = 1 then (Real.sqrt y : ℂ) *
    Complex.exp (-2 * (Real.pi : ℂ) * (1 - a) * (y : ℂ)) else 0) -
  (if j = -1 then (Real.sqrt y : ℂ) *
    Complex.exp (-2 * (Real.pi : ℂ) * (1 - a) * (y : ℂ)) else 0) +
  (if j = 0 then (Real.sqrt y : ℂ) *
    Complex.exp (-2 * (Real.pi : ℂ) * (2 - a) * (y : ℂ)) else 0)

/-- The complete four-seed continuum is ordinarily integrable at every
positive temperature, even though its inputs have negative energies. -/
theorem integrable_vacuumFullKernel_laplace (a y : ℝ) (hy : 0 < y) (j : ℤ) :
    Integrable (fun e : ℝ =>
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) * vacuumFullKernel a e j)
        (referenceMeasure j) := by
  simpa only [vacuumFullKernel, mul_add, mul_sub, Pi.sub_apply, Pi.add_apply] using!
    (((integrable_fullKernelHol_laplace y hy (-a) j 0).sub
      (integrable_fullKernelHol_laplace y hy (1 - a) j 1)).sub
      (integrable_fullKernelHol_laplace y hy (1 - a) j (-1))).add
      (integrable_fullKernelHol_laplace y hy (2 - a) j 0)

/-- Ordinary integrability makes the four signed kernel transforms additive. -/
theorem integral_vacuumFullKernel_laplace_eq_four_seed
    (a y : ℝ) (hy : 0 < y) (j : ℤ) :
    (∫ e : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
      vacuumFullKernel a e j ∂referenceMeasure j) =
    (∫ e : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
      fullKernelHol j 0 (e : ℂ) (-a) ∂referenceMeasure j) -
    (∫ e : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
      fullKernelHol j 1 (e : ℂ) (1 - a) ∂referenceMeasure j) -
    (∫ e : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
      fullKernelHol j (-1) (e : ℂ) (1 - a) ∂referenceMeasure j) +
    (∫ e : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
      fullKernelHol j 0 (e : ℂ) (2 - a) ∂referenceMeasure j) := by
  have h0 := integrable_fullKernelHol_laplace y hy (-a) j 0
  have hp := integrable_fullKernelHol_laplace y hy (1 - a) j 1
  have hm := integrable_fullKernelHol_laplace y hy (1 - a) j (-1)
  have h2 := integrable_fullKernelHol_laplace y hy (2 - a) j 0
  simp only [vacuumFullKernel, mul_add, mul_sub]
  rw [integral_add ((h0.sub' hp).sub' hm) h2,
    integral_sub (h0.sub' hp) hm, integral_sub h0 hp]

/-- Full ordinary Fourier–Laplace output of the actual modular vacuum. The
threshold atom is separate from its ordinary density on `e > |j|`. -/
theorem vacuumFourierCoefficient_eq_full_laplace
    (a y : ℝ) (hy : 0 < y) (j : ℤ) :
    vacuumFourierCoefficient a y hy j =
      vacuumDirectFourier a y j +
      (if j = 0 then -6 * (Real.sqrt y : ℂ) else 0) +
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          vacuumFullKernel a e j ∂referenceMeasure j := by
  have h0 := integrable_fullKernelHol_laplace y hy (-a) j 0
  have hp := integrable_fullKernelHol_laplace y hy (1 - a) j 1
  have hm := integrable_fullKernelHol_laplace y hy (1 - a) j (-1)
  have h2 := integrable_fullKernelHol_laplace y hy (2 - a) j 0
  have hsplit := integral_add ((h0.sub' hp).sub' hm) h2
  rw [integral_sub (h0.sub' hp) hm, integral_sub h0 hp] at hsplit
  rw [vacuumFourierCoefficient_eq_four_seed]
  have f0 := generalThresholdFourierCoefficient_eq_full_laplace y hy (-a) j 0
  have fp := generalThresholdFourierCoefficient_eq_full_laplace y hy (1 - a) j 1
  have fm := generalThresholdFourierCoefficient_eq_full_laplace y hy (1 - a) j (-1)
  have f2 := generalThresholdFourierCoefficient_eq_full_laplace y hy (2 - a) j 0
  push_cast at f0 fp fm f2
  rw [f0, fp, fm, f2]
  simp only [vacuumFullKernel, mul_add, mul_sub]
  rw [hsplit]
  simp only [vacuumDirectFourier, scalarThresholdCoefficient_zero,
    scalarThresholdCoefficient_one, scalarThresholdCoefficient_neg_one, mul_sub]
  split_ifs <;> ring

/-- The density estimated by the real vacuum lower bounds is the same density
in the Fourier output of the actual modular completion. -/
theorem vacuumFourierCoefficient_eq_real_laplace
    (a y : ℝ) (hy : 0 < y) (j : ℤ) :
    vacuumFourierCoefficient a y hy j =
      vacuumDirectFourier a y j +
      (if j = 0 then -6 * (Real.sqrt y : ℂ) else 0) +
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          (vacuumNumerator a e j : ℂ) ∂referenceMeasure j := by
  simpa only [vacuumNumerator_coe_eq] using
    vacuumFourierCoefficient_eq_full_laplace a y hy j

end GapFamily.Analytic
