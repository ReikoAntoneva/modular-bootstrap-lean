import GapFamily.Analytic.Poincare.Fourier.PoincareFourierBesselTransform
import GapFamily.Analytic.Bessel.BesselCoshOrderNonzero
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

noncomputable section
namespace GapFamily.Analytic.PoincareCentralFactor
open Set MeasureTheory BesselCoshOrder PoincareFourierRemainder

/-- The literal entire Gamma and pi factor in the central Fourier coefficient. -/
def centralGammaFactor (κ : ℂ) : ℂ :=
  2 * (Real.pi : ℂ) ^ ((1 / 2 : ℂ) + κ) / Complex.Gamma ((1 / 2 : ℂ) + κ)

/-- Reciprocal Gamma supplies entire analyticity even at the zeros of the reciprocal. -/
theorem centralGammaFactor_analyticAt (κ : ℂ) : AnalyticAt ℂ centralGammaFactor κ := by
  have ha : Differentiable ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) :=
    (differentiable_const _).add differentiable_id
  have hp : Differentiable ℂ (fun w : ℂ => (Real.pi : ℂ) ^ ((1 / 2 : ℂ) + w)) :=
    ha.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hg : Differentiable ℂ (fun w : ℂ => (Complex.Gamma ((1 / 2 : ℂ) + w))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp ha
  change AnalyticAt ℂ (fun w : ℂ =>
    2 * (Real.pi : ℂ) ^ ((1 / 2 : ℂ) + w) / Complex.Gamma ((1 / 2 : ℂ) + w)) κ
  convert! (((differentiable_const 2).mul hp).mul hg).analyticAt κ using 1

/-- The half-Gamma special value gives exactly the coefficient two at threshold. -/
theorem centralGammaFactor_zero : centralGammaFactor 0 = 2 := by
  have hp : (Real.pi : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  simp only [centralGammaFactor, add_zero, Complex.Gamma_one_half_eq]
  exact mul_div_cancel_right₀ 2 hp

/-- Evaluation of the genuine compact-argument integral proves scalar order analyticity. -/
theorem besselK_analyticAt {t : ℝ} (ht : 0 < t) (κ : ℂ) :
    AnalyticAt ℂ (fun w => besselK w t) κ := by
  let p : Icc t t := ⟨t, le_rfl, le_rfl⟩
  have he := ((ContinuousMap.evalCLM ℂ p).analyticAt (besselKOn t t κ)).comp
    (besselKOn_analyticAt t t ht κ)
  simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, besselKOn_apply t t ht, p] using he

/-- The original positive order-zero integral stays positive at every positive argument. -/
theorem besselK0_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < besselK0 t := by
  by_cases ht1 : 1 ≤ t
  · exact besselK0_pos ht1
  · have hmono : besselK0 1 ≤ besselK0 t :=
      besselK0_antitoneOn_pos ht (by simp) (le_of_not_ge ht1)
    exact (besselK0_pos (t := 1) le_rfl).trans_le hmono

/-- The actual central Fourier factor in shifted spectral coordinates. -/
def centralFourierFactor (y : ℝ) (j : ℤ) (κ : ℂ) : ℂ :=
  centralGammaFactor κ * ((|(j : ℝ)| : ℝ) : ℂ) ^ κ * (Real.sqrt y : ℂ) *
    besselK κ (2 * Real.pi * |(j : ℝ)| * y)

/-- The actual central Fourier factor is entire in the shifted spectral parameter. -/
theorem centralFourierFactor_analyticAt {y : ℝ} (hy : 0 < y) {j : ℤ} (hj : j ≠ 0)
    (κ : ℂ) : AnalyticAt ℂ (centralFourierFactor y j) κ := by
  have hn : 0 < |(j : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hj)
  have hnc : ((|(j : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hp : AnalyticAt ℂ (fun w : ℂ => ((|(j : ℝ)| : ℝ) : ℂ) ^ w) κ :=
    (differentiable_id.const_cpow (Or.inl hnc)).analyticAt κ
  have ht : 0 < 2 * Real.pi * |(j : ℝ)| * y := by positivity
  exact (((centralGammaFactor_analyticAt κ).mul hp).mul analyticAt_const).mul
    (besselK_analyticAt ht κ)

/-- The threshold value is exactly the original order-zero Fourier denominator. -/
theorem centralFourierFactor_zero (y : ℝ) (j : ℤ) :
    centralFourierFactor y j 0 =
      2 * (Real.sqrt y : ℂ) * (besselK0 (2 * Real.pi * |(j : ℝ)| * y) : ℂ) := by
  simp only [centralFourierFactor, centralGammaFactor_zero, Complex.cpow_zero, mul_one,
    besselK_zero]

/-- Positive height and nonzero frequency give a genuinely nonzero threshold factor. -/
theorem centralFourierFactor_zero_ne_zero {y : ℝ} (hy : 0 < y) {j : ℤ} (hj : j ≠ 0) :
    centralFourierFactor y j 0 ≠ 0 := by
  have hn : 0 < |(j : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hj)
  have ht : 0 < 2 * Real.pi * |(j : ℝ)| * y := by positivity
  have hs : (Real.sqrt y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  have hb : (besselK0 (2 * Real.pi * |(j : ℝ)| * y) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (besselK0_pos_of_pos ht).ne'
  rw [centralFourierFactor_zero]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hs) hb

/-- On the genuine Fourier-integrability half-plane the entire factor equals the actual integral. -/
theorem centralFourierFactor_eq_integral {y : ℝ} (hy : 0 < y) {j : ℤ} (hj : j ≠ 0)
    {κ : ℂ} (hκ : 0 < κ.re) :
    centralFourierFactor y j κ =
      ∫ t : ℝ, centralFourierKernel y j ((1 / 2 : ℂ) + κ) t := by
  have hs : (1 / 2 : ℝ) < ((1 / 2 : ℂ) + κ).re := by
    norm_num [Complex.add_re]
    linarith
  have he : (1 / 2 : ℂ) + κ - 1 / 2 = κ := by ring
  simpa only [centralFourierFactor, centralGammaFactor, he] using
    (integral_centralFourierKernel_eq_besselK hy hj hs).symm

end GapFamily.Analytic.PoincareCentralFactor
