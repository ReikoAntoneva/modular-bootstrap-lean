import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The ordinary order-zero modified Bessel integral

The definition is the actual scalar integral used in the Fourier coefficient.
The shifted integrand is auxiliary and retains the endpoint singularity.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

/-- The source's actual integrand for the order-zero modified Bessel function. -/
def besselK0Integrand (t v : ℝ) : ℝ :=
  Real.exp (-t * v) / Real.sqrt (v ^ 2 - 1)

/-- The ordinary integral over `(1,∞)`; later lemmas prove its integrability. -/
def besselK0 (t : ℝ) : ℝ := ∫ v : ℝ in Ioi 1, besselK0Integrand t v

/-- Translation `v=1+w` separates the endpoint singularity and thermal factor. -/
def besselK0ShiftIntegrand (t w : ℝ) : ℝ :=
  Real.exp (-t * w) / Real.sqrt (w * (w + 2))

@[simp] theorem besselK0Integrand_add_one (t w : ℝ) :
    besselK0Integrand t (w + 1) = Real.exp (-t) * besselK0ShiftIntegrand t w := by
  unfold besselK0Integrand besselK0ShiftIntegrand
  rw [show -t * (w + 1) = -t + -t * w by ring, Real.exp_add,
    show (w + 1) ^ 2 - 1 = w * (w + 2) by ring]
  ring

end GapFamily.Analytic
