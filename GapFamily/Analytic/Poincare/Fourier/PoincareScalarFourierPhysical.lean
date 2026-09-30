import GapFamily.Analytic.Poincare.Fourier.PoincareScalarCentralIntegral
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierCentralSplit
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierContinuation
import GapFamily.Analytic.Arithmetic.KloostermanZeroContinuation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

noncomputable section
namespace GapFamily.Analytic.PoincareScalarFourier
open Set Filter MeasureTheory CuspFourierCutoff PoincareCanonical
open PoincareFourierContinuation PoincareFourierRemainder
open scoped Topology

/-- The actual scalar central factor, before cancellation at the threshold. -/
def scalarCentralContinuation (y : ℝ) (J : ℤ) (κ : ℂ) : ℂ :=
  (y : ℂ) ^ ((1 / 2 : ℂ) - κ) * (Real.sqrt Real.pi : ℂ) * Complex.Gamma κ /
    Complex.Gamma (exponent κ) * zeroFrequencyKloostermanContinuation J (exponent κ)

/-- The literal Gamma/arithmetic expression is analytic on the open positive half-plane. -/
theorem scalarCentralContinuation_analyticAt {y : ℝ} (hy : 0 < y)
    (J : ℤ) (hJ : J ≠ 0) {κ : ℂ} (hκ : 0 < κ.re) :
    AnalyticAt ℂ (scalarCentralContinuation y J) κ := by
  have hg : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change 0 < z.re at hz
    linarith
  have haG : AnalyticAt ℂ Complex.Gamma κ :=
    hg.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hκ)
  have hp : AnalyticAt ℂ (fun z : ℂ => (y : ℂ) ^ ((1 / 2 : ℂ) - z)) κ :=
    (((differentiable_const _).sub differentiable_id).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).analyticAt κ
  have hex : AnalyticAt ℂ exponent κ := analyticAt_const.add analyticAt_id
  have hinv : AnalyticAt ℂ (fun z : ℂ => (Complex.Gamma (exponent z))⁻¹) κ :=
    ((Complex.differentiable_one_div_Gamma.comp
      ((differentiable_const _).add differentiable_id))).analyticAt κ
  have hz : AnalyticAt ℂ (fun z => zeroFrequencyKloostermanContinuation J (exponent z)) κ := by
    apply (zeroFrequencyKloostermanContinuation_analyticAt J ?_ ?_).comp hex
    · simp only [exponent, Complex.add_re]
      norm_num
      linarith
    · intro h
      exact (hJ h).elim
  change AnalyticAt ℂ (fun z => (y : ℂ) ^ ((1 / 2 : ℂ) - z) *
    (Real.sqrt Real.pi : ℂ) * Complex.Gamma z / Complex.Gamma (exponent z) *
      zeroFrequencyKloostermanContinuation J (exponent z)) κ
  convert! (((hp.mul analyticAt_const).mul haG).mul hinv).mul hz using 1

/-- The scalar formula agrees with the actual ordinary coefficient in the convergent region. -/
theorem continuedFourierCoefficient_zero_eq_central_add_remainder_common
    (y : ℝ) (hy : 0 < y) (J : ℤ) (hJ : J ≠ 0) {κ : ℂ}
    (hκ : (1 / 2 : ℝ) < κ.re) :
    continuedFourierCoefficient y hy 0 J κ = scalarCentralContinuation y J κ +
      fourierRemainder y 0 J (exponent κ) := by
  have hs : 1 < (exponent κ).re := by
    simp only [exponent, Complex.add_re]
    norm_num
    linarith
  rw [continuedFourierCoefficient_eq_series y hy 0 J hκ,
    complexPoincareSeries_fourier_eq_central_add_remainder hy 0 J hs,
    ite_eq_right (Ne.symm hJ), zero_add,
    integral_centralFourierKernel_zero_eq_gamma hy (by linarith),
    ← zeroFrequencyKloostermanContinuation_eq_series J hs]
  have h1 : 1 - exponent κ = (1 / 2 : ℂ) - κ := by dsimp [exponent]; ring
  have h2 : exponent κ - 1 / 2 = κ := by dsimp [exponent]; ring
  rw [h1, h2]
  rfl

/-- Analytic uniqueness identifies the actual scalar coefficient throughout the punctured
physical half-plane; no ordinary central integral is asserted at the threshold. -/
theorem continuedFourierCoefficient_zero_eq_central_add_remainder
    (y : ℝ) (hy : 0 < y) (J : ℤ) (hJ : J ≠ 0) {κ : ℂ}
    (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) :
    continuedFourierCoefficient y hy 0 J κ = scalarCentralContinuation y J κ +
      fourierRemainder y 0 J (exponent κ) := by
  let U : Set ℂ := {z | 0 < z.re ∧ z ≠ (1 / 2 : ℂ)}
  have hf : AnalyticOnNhd ℂ (continuedFourierCoefficient y hy 0 J) U := by
    intro z hz
    exact analyticOnNhd_continuedFourierCoefficient y hy 0 J z (Or.inr hz)
  have hg : AnalyticOnNhd ℂ (fun z => scalarCentralContinuation y J z +
      fourierRemainder y 0 J (exponent z)) U := by
    intro z hz
    apply (scalarCentralContinuation_analyticAt hy J hJ hz.1).add
    apply (analyticAt_fourierRemainder hy 0 J ?_).comp
      (show AnalyticAt ℂ exponent z from analyticAt_const.add analyticAt_id)
    simp only [exponent, Complex.add_re]
    norm_num
    linarith [hz.1]
  have ht : (2 : ℂ) ∈ U := by norm_num [U]
  have he : continuedFourierCoefficient y hy 0 J =ᶠ[𝓝 (2 : ℂ)]
      (fun z => scalarCentralContinuation y J z + fourierRemainder y 0 J (exponent z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact continuedFourierCoefficient_zero_eq_central_add_remainder_common y hy J hJ hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_puncturedRightHalfPlane
    ht he ⟨hκ, hp⟩

end GapFamily.Analytic.PoincareScalarFourier
