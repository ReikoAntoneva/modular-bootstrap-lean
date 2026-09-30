import BTZEntropy.Analytic.ComplexKernel
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace BTZEntropy

/-- The compact smoothing kernel tilted by a real Boltzmann parameter. -/
def tiltedKernelSchwartz (φ : SmoothKernel) (β : ℝ) : SchwartzMap ℝ ℂ :=
  ((φ.compactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right
    (f' := fun u : ℝ => Complex.exp ((β : ℂ) * (u : ℂ)))).toSchwartzMap
    ((Complex.ofRealCLM.contDiff.comp φ.smooth).mul
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp))

@[simp] theorem tiltedKernelSchwartz_apply (φ : SmoothKernel) (β u : ℝ) :
    tiltedKernelSchwartz φ β u = (φ u : ℂ) * Complex.exp ((β : ℂ) * (u : ℂ)) := rfl

@[simp] theorem tiltedKernelSchwartz_coe (φ : SmoothKernel) (β : ℝ) :
    (tiltedKernelSchwartz φ β : ℝ → ℂ) =
      fun u => (φ u : ℂ) * Complex.exp ((β : ℂ) * (u : ℂ)) := rfl

/-- The Fourier transform of the tilted kernel is absolutely integrable. -/
theorem integrable_fourier_tiltedKernel (φ : SmoothKernel) (β : ℝ) :
    Integrable (FourierTransform.fourier
      (fun u : ℝ => (φ u : ℂ) * Complex.exp ((β : ℂ) * (u : ℂ)))) := by
  exact (𝓕 (tiltedKernelSchwartz φ β)).integrable (μ := volume)

/-- The inverse Fourier transform of the tilted kernel is absolutely integrable. -/
theorem integrable_fourierInv_tiltedKernel (φ : SmoothKernel) (β : ℝ) :
    Integrable (FourierTransformInv.fourierInv
      (fun u : ℝ => (φ u : ℂ) * Complex.exp ((β : ℂ) * (u : ℂ)))) := by
  have h := (𝓕⁻ (tiltedKernelSchwartz φ β)).integrable (μ := volume)
  rw [SchwartzMap.fourierInv_coe] at h
  exact h

end BTZEntropy
