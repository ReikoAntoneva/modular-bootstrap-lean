import GapFamily.Analytic.Arithmetic.KloostermanZeroContinuation
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

noncomputable section

namespace GapFamily.Analytic.PoincareScalarFourier

open Complex Filter
open scoped Topology

/-- The regular Gamma prefactor at the spectral threshold has value one. -/
theorem zeroFrequencyGammaRegularized_tendsto_half :
    Tendsto (fun s : ℂ =>
      (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s + 1 / 2) / Complex.Gamma s)
      (𝓝 (1 / 2)) (𝓝 1) := by
  have hhalf : Complex.Gamma (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.Gamma_ofReal, Real.Gamma_one_half_eq]
  have hroot : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hg : ContinuousAt Complex.Gamma ((1 / 2 : ℂ) + 1 / 2) := by
    norm_num
    exact Complex.continuousAt_Gamma_one
  have hi : ContinuousAt (fun s : ℂ => (Complex.Gamma s)⁻¹) (1 / 2) :=
    Complex.differentiable_one_div_Gamma.continuous.continuousAt
  have harg : ContinuousAt (fun s : ℂ => s + 1 / 2) (1 / 2) := by fun_prop
  have h := ((hg.comp (f := fun s : ℂ => s + 1 / 2) harg).const_mul
    (Real.sqrt Real.pi : ℂ)).mul hi
  have hc : ContinuousAt (fun s : ℂ =>
      (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s + 1 / 2) / Complex.Gamma s)
      (1 / 2) := by
    convert h using 1
    ext s
    exact div_eq_mul_inv _ _
  have hv : (Real.sqrt Real.pi : ℂ) * Complex.Gamma ((1 / 2 : ℂ) + 1 / 2) /
      Complex.Gamma (1 / 2) = 1 := by
    rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
      Complex.Gamma_one, mul_one, hhalf, div_self hroot]
  simpa only [hv] using hc.tendsto

/-- The genuine punctured Gamma product has the exact arithmetic threshold value. -/
theorem zeroFrequencyGammaContinuation_tendsto_half (J : ℤ) :
    Tendsto (fun s : ℂ =>
      (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s *
        zeroFrequencyKloostermanContinuation J s)
      (𝓝[≠] (1 / 2))
      (𝓝 (if J = 0 then -1 else 2 * (J.natAbs.divisors.card : ℂ))) := by
  have h := (zeroFrequencyGammaRegularized_tendsto_half.mono_left
    nhdsWithin_le_nhds).mul (zeroFrequencyKloostermanContinuation_div_tendsto_half J)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - 1 / 2 ≠ 0 := sub_ne_zero.mpr hs
  rw [show s + 1 / 2 = (s - 1 / 2) + 1 by ring,
    Complex.Gamma_add_one _ hs']
  calc
    _ = ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (s - 1 / 2) /
        Complex.Gamma s * zeroFrequencyKloostermanContinuation J s) *
        ((s - 1 / 2) / (s - 1 / 2)) := by ring
    _ = _ := by rw [div_self hs', mul_one]

/-- The same limit holds for the literal ordinary divisor/zeta quotient. -/
theorem zeroFrequencyGammaQuotient_tendsto_half (J : ℤ) (hJ : J ≠ 0) :
    Tendsto (fun s : ℂ =>
      (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s *
        (zeroFrequencyDivisorFactor J s / riemannZeta (2 * s)))
      (𝓝[≠] (1 / 2)) (𝓝 (2 * (J.natAbs.divisors.card : ℂ))) := by
  have h := zeroFrequencyGammaContinuation_tendsto_half J
  simp only [ite_eq_right hJ] at h
  apply h.congr'
  have h0 : ∀ᶠ s : ℂ in 𝓝[≠] (1 / 2), s ≠ 0 :=
    (eventually_ne_nhds (by norm_num : (1 / 2 : ℂ) ≠ 0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hs
  rw [zeroFrequencyKloostermanContinuation_eq_quotient J hs0 hs, ite_eq_right hJ]

end GapFamily.Analytic.PoincareScalarFourier
