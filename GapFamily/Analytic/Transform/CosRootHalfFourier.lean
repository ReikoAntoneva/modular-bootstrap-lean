import GapFamily.Analytic.Transform.CosRootHalfProfileBound
import GapFamily.Analytic.Transform.CosRootHalfLaplace
import Mathlib.Analysis.Fourier.FourierTransform

/-! Exact Fourier transform of the actual damped half-line cosRoot profile. -/
noncomputable section
namespace GapFamily.Analytic.CosRootLaplace
open Set MeasureTheory
open scoped FourierTransform

/-- The literal complex Laplace rate of the real Fourier frequency. -/
def halfFourierRate (a t : ℝ) : ℂ := (a : ℂ) + (2 * Real.pi * t : ℝ) * Complex.I

/-- Actual Gaussian value of the Fourier integral. -/
def halfFourierValue (a : ℝ) (A : ℂ) (t : ℝ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * (halfFourierRate a t) ^ (-(1 / 2 : ℂ)) *
    Complex.exp (-A / (4 * halfFourierRate a t))

/-- The actual half-profile Fourier integrand is the literal half-line Laplace integrand. -/
theorem halfProfile_fourier_integrand (a : ℝ) (A : ℂ) (t x : ℝ) :
    Complex.exp ((-2 * Real.pi * x * t : ℝ) * Complex.I) • halfProfile a A x =
      (Ioi (0 : ℝ)).indicator (cosRootHalfLaplaceIntegrand A (halfFourierRate a t)) x := by
  change Complex.exp ((-2 * Real.pi * x * t : ℝ) * Complex.I) • halfProfile a A x =
    if 0 < x then cosRootHalfLaplaceIntegrand A (halfFourierRate a t) x else 0
  by_cases hx : 0 < x
  · simp only [halfProfile, ite_eq_left hx, cosRootHalfLaplaceIntegrand,
      smul_eq_mul]
    have he : Complex.exp (-(halfFourierRate a t) * (x : ℂ)) =
        Complex.exp ((-2 * Real.pi * x * t : ℝ) * Complex.I) *
          Complex.exp (-(a : ℂ) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold halfFourierRate
      push_cast
      ring_nf
    rw [he]
    ring_nf
  · simp [halfProfile, hx]

/-- Ordinary Fourier transformation of the genuine integrable half-profile. -/
theorem fourier_halfProfile {a : ℝ} (ha : 0 < a) (A : ℂ) (t : ℝ) :
    𝓕 (halfProfile a A) t = halfFourierValue a A t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [halfProfile_fourier_integrand]
  rw [integral_indicator measurableSet_Ioi]
  exact integral_cosRootHalfLaplaceIntegrand A (by simpa [halfFourierRate] using ha)

/-- Ordinary Fourier subtraction is legitimate for the concrete integrable profiles. -/
theorem fourier_regularHalfProfile {a : ℝ} (ha : 0 < a) (A : ℂ) (t : ℝ) :
    𝓕 (regularHalfProfile a A) t = halfFourierValue a A t - halfFourierValue a 0 t := by
  have h : 𝓕 (regularHalfProfile a A) t =
      𝓕 (halfProfile a A) t - 𝓕 (halfProfile a 0) t := by
    simp only [Real.fourier_eq, regularHalfProfile, smul_sub]
    rw [integral_sub]
    · exact (Real.fourierIntegral_convergent_iff t).mpr (integrable_halfProfile ha A)
    · exact (Real.fourierIntegral_convergent_iff t).mpr (integrable_halfProfile ha 0)
  rw [h, fourier_halfProfile ha A t, fourier_halfProfile ha 0 t]

/-- Reflection changes exactly the sign of the Fourier frequency. -/
theorem fourier_halfProfile_reflect {a : ℝ} (ha : 0 < a) (A : ℂ) (t : ℝ) :
    𝓕 (fun x : ℝ => halfProfile a A (-x)) t = halfFourierValue a A (-t) := by
  change 𝓕 (halfProfile a A ∘ LinearIsometryEquiv.neg ℝ) t = _
  rw [Real.fourier_comp_linearIsometry]
  exact fourier_halfProfile ha A (-t)

theorem fourier_regularHalfProfile_reflect {a : ℝ} (ha : 0 < a) (A : ℂ) (t : ℝ) :
    𝓕 (fun x : ℝ => regularHalfProfile a A (-x)) t =
      halfFourierValue a A (-t) - halfFourierValue a 0 (-t) := by
  change 𝓕 (regularHalfProfile a A ∘ LinearIsometryEquiv.neg ℝ) t = _
  rw [Real.fourier_comp_linearIsometry]
  exact fourier_regularHalfProfile ha A (-t)

end GapFamily.Analytic.CosRootLaplace
