import GapFamily.Analytic.Poincare.Fourier.PoincareScalarFourierPhysical
import GapFamily.Analytic.Poincare.Fourier.PoincareZeroFrequencyGammaLimit

noncomputable section
namespace GapFamily.Analytic.PoincareScalarFourier
open Set Filter MeasureTheory CuspFourierCutoff PoincareCanonical
open PoincareFourierContinuation PoincareFourierRemainder
open scoped Topology

/-- The actual threshold scalar Fourier coefficient has exactly the divisor normalization,
plus the genuinely integrable phase-subtracted remainder. -/
theorem thresholdFourierCoefficient_zero_eq_divisor_add_remainder
    (y : ℝ) (hy : 0 < y) (J : ℤ) (hJ : J ≠ 0) :
    thresholdFourierCoefficient y hy 0 J =
      (Real.sqrt y : ℂ) * (2 * (J.natAbs.divisors.card : ℂ)) +
        fourierRemainder y 0 J (1 / 2 : ℂ) := by
  let u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 3)
  let k : ℕ → ℂ := fun n => (u n : ℂ)
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [u, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_add_atTop_iff_nat 3).2
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hk : Tendsto k atTop (𝓝 0) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hu
  have hpos (n : ℕ) : 0 < (k n).re := by dsimp [k, u]; positivity
  have hp (n : ℕ) : k n ≠ (1 / 2 : ℂ) := by
    have hd : 0 < (n : ℝ) + 3 := by positivity
    have hlt : 1 / ((n : ℝ) + 3) < (1 / 2 : ℝ) :=
      (div_lt_iff₀ hd).2 (by have hn := Nat.cast_nonneg (α := ℝ) n; nlinarith)
    intro h
    change (u n : ℂ) = (1 / 2 : ℂ) at h
    have hr : u n = (1 / 2 : ℝ) := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h
    exact (ne_of_lt hlt) hr
  have hex : Tendsto (fun n => exponent (k n)) atTop (𝓝 (1 / 2 : ℂ)) := by
    simpa only [exponent, add_zero] using tendsto_const_nhds.add hk
  have hex' : Tendsto (fun n => exponent (k n)) atTop (𝓝[≠] (1 / 2 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hex, Eventually.of_forall ?_⟩
    intro n
    change exponent (k n) ≠ 1 / 2
    intro h
    have hz : k n = 0 := by dsimp [exponent] at h; linear_combination h
    have hh := hpos n
    rw [hz] at hh
    simp at hh
  have hgamma := (zeroFrequencyGammaContinuation_tendsto_half J).comp hex'
  simp only [ite_eq_right hJ] at hgamma
  have hpow : Tendsto (fun n => (y : ℂ) ^ ((1 / 2 : ℂ) - k n)) atTop
      (𝓝 (Real.sqrt y : ℂ)) := by
    have hc : ContinuousAt (fun z : ℂ => (y : ℂ) ^ ((1 / 2 : ℂ) - z)) 0 :=
      ((((differentiable_const _).sub differentiable_id).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).continuous.continuousAt)
    have hp0 : (y : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt y : ℂ) := by
      calc
        _ = ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
          simpa using (Complex.ofReal_cpow hy.le (1 / 2 : ℝ)).symm
        _ = _ := by rw [← Real.sqrt_eq_rpow]
    simpa only [Function.comp_def, sub_zero, hp0] using hc.tendsto.comp hk
  have hcentral : Tendsto (fun n => scalarCentralContinuation y J (k n)) atTop
      (𝓝 ((Real.sqrt y : ℂ) * (2 * (J.natAbs.divisors.card : ℂ)))) := by
    convert hpow.mul hgamma using 1
    funext n
    dsimp [scalarCentralContinuation]
    rw [show exponent (k n) - 1 / 2 = k n by dsimp [exponent]; ring]
    ring
  have hrem : Tendsto (fun n => fourierRemainder y 0 J (exponent (k n))) atTop
      (𝓝 (fourierRemainder y 0 J (1 / 2 : ℂ))) :=
    (analyticAt_fourierRemainder hy 0 J (by norm_num : 0 < (1 / 2 : ℂ).re)).continuousAt.tendsto.comp hex
  have hcoef : Tendsto (fun n => continuedFourierCoefficient y hy 0 J (k n)) atTop
      (𝓝 (thresholdFourierCoefficient y hy 0 J)) := by
    simpa only [Function.comp_def, continuedFourierCoefficient_zero] using
      (analyticAt_continuedFourierCoefficient_zero y hy 0 J).continuousAt.tendsto.comp hk
  have heq : (fun n => continuedFourierCoefficient y hy 0 J (k n)) =
      (fun n => scalarCentralContinuation y J (k n) + fourierRemainder y 0 J (exponent (k n))) := by
    funext n
    exact continuedFourierCoefficient_zero_eq_central_add_remainder y hy J hJ (hpos n) (hp n)
  rw [heq] at hcoef
  exact tendsto_nhds_unique hcoef (hcentral.add hrem)

end GapFamily.Analytic.PoincareScalarFourier
