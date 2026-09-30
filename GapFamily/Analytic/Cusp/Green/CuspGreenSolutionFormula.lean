import GapFamily.Analytic.Cusp.Green.CuspGreen
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite-integral solution of the forced scalar cusp equation

The formula uses ordinary interval integrals. Its derivative certificates
establish the differential equation directly, without an operator-domain claim.
-/

noncomputable section

open MeasureTheory
open scoped Interval Topology

namespace GapFamily.Analytic

/-- The finite-integral variation-of-parameters formula with Dirichlet reflection. -/
def cuspGreenSolutionFormula (t₀ T : ℝ) (κ : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-κ * (t : ℂ)) *
      (∫ u in t₀..t, Complex.exp (κ * (u : ℂ)) * f u) +
    Complex.exp (κ * (t : ℂ)) *
      (∫ u in t..T, Complex.exp (-κ * (u : ℂ)) * f u) -
    Complex.exp (-κ * ((t : ℂ) - 2 * (t₀ : ℂ))) *
      (∫ u in t₀..T, Complex.exp (-κ * (u : ℂ)) * f u)) / (2 * κ)

/-- The first derivative, with the cancelling endpoint terms removed. -/
def cuspGreenSolutionFormulaDeriv
    (t₀ T : ℝ) (κ : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (-Complex.exp (-κ * (t : ℂ)) *
      (∫ u in t₀..t, Complex.exp (κ * (u : ℂ)) * f u) +
    Complex.exp (κ * (t : ℂ)) *
      (∫ u in t..T, Complex.exp (-κ * (u : ℂ)) * f u) +
    Complex.exp (-κ * ((t : ℂ) - 2 * (t₀ : ℂ))) *
      (∫ u in t₀..T, Complex.exp (-κ * (u : ℂ)) * f u)) / 2

private theorem cuspSolution_exp_hasDerivAt (κ : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (κ * (u : ℂ)))
      (κ * Complex.exp (κ * (t : ℂ))) t := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (κ * z))
      (Complex.exp (κ * (t : ℂ)) * (κ * 1)) (t : ℂ) :=
    (Complex.hasDerivAt_exp _).comp _ ((hasDerivAt_id _).const_mul κ)
  simpa only [mul_one, mul_comm] using h.comp_ofReal

private theorem cuspSolution_reflect_hasDerivAt (t₀ : ℝ) (κ : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (-κ * ((u : ℂ) - 2 * (t₀ : ℂ))))
      (-κ * Complex.exp (-κ * ((t : ℂ) - 2 * (t₀ : ℂ)))) t := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (-κ * (z - 2 * (t₀ : ℂ))))
      (Complex.exp (-κ * ((t : ℂ) - 2 * (t₀ : ℂ))) * (-κ * 1)) (t : ℂ) :=
    (Complex.hasDerivAt_exp _).comp _
      (((hasDerivAt_id _).sub_const (2 * (t₀ : ℂ))).const_mul (-κ))
  simpa only [mul_one, mul_comm] using h.comp_ofReal

private theorem cuspSolution_integrand_continuous
    (κ : ℂ) {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (fun u : ℝ => Complex.exp (κ * (u : ℂ)) * f u) :=
  (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul hf

/-- Actual first derivative of the ordinary finite-integral formula. -/
theorem hasDerivAt_cuspGreenSolutionFormula
    (t₀ T : ℝ) {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ}
    (hf : Continuous f) (t : ℝ) :
    HasDerivAt (cuspGreenSolutionFormula t₀ T κ f)
      (cuspGreenSolutionFormulaDeriv t₀ T κ f t) t := by
  have hp := cuspSolution_integrand_continuous κ hf
  have hm := cuspSolution_integrand_continuous (-κ) hf
  have ha := intervalIntegral.integral_hasDerivAt_right
    (hp.intervalIntegrable t₀ t) (hp.stronglyMeasurableAtFilter volume (𝓝 t)) hp.continuousAt
  have hb := intervalIntegral.integral_hasDerivAt_left
    (hm.intervalIntegrable t T) (hm.stronglyMeasurableAtFilter volume (𝓝 t)) hm.continuousAt
  have hd := (((cuspSolution_exp_hasDerivAt (-κ) t).mul ha).add
    ((cuspSolution_exp_hasDerivAt κ t).mul hb)).sub
      ((cuspSolution_reflect_hasDerivAt t₀ κ t).mul_const
        (∫ u in t₀..T, Complex.exp (-κ * (u : ℂ)) * f u))
  apply (hd.div_const (2 * κ)).congr_deriv
  unfold cuspGreenSolutionFormulaDeriv
  field_simp [hκ]
  ring

/-- Actual derivative of the first derivative; the two endpoint terms give the source. -/
theorem hasDerivAt_cuspGreenSolutionFormulaDeriv
    (t₀ T : ℝ) {κ : ℂ} {f : ℝ → ℂ}
    (hf : Continuous f) (t : ℝ) :
    HasDerivAt (cuspGreenSolutionFormulaDeriv t₀ T κ f)
      (κ ^ 2 * cuspGreenSolutionFormula t₀ T κ f t - f t) t := by
  have hp := cuspSolution_integrand_continuous κ hf
  have hm := cuspSolution_integrand_continuous (-κ) hf
  have ha := intervalIntegral.integral_hasDerivAt_right
    (hp.intervalIntegrable t₀ t) (hp.stronglyMeasurableAtFilter volume (𝓝 t)) hp.continuousAt
  have hb := intervalIntegral.integral_hasDerivAt_left
    (hm.intervalIntegrable t T) (hm.stronglyMeasurableAtFilter volume (𝓝 t)) hm.continuousAt
  have hd := ((((cuspSolution_exp_hasDerivAt (-κ) t).neg.mul ha).add
    ((cuspSolution_exp_hasDerivAt κ t).mul hb)).add
      ((cuspSolution_reflect_hasDerivAt t₀ κ t).mul_const
        (∫ u in t₀..T, Complex.exp (-κ * (u : ℂ)) * f u))).div_const 2
  have hcancel : Complex.exp (-κ * (t : ℂ)) * Complex.exp (κ * (t : ℂ)) = 1 := by
    rw [← Complex.exp_add, show -κ * (t : ℂ) + κ * t = 0 by ring, Complex.exp_zero]
  apply hd.congr_deriv
  unfold cuspGreenSolutionFormula
  dsimp only [Pi.neg_apply]
  simp only [neg_mul, mul_neg, neg_neg]
  field_simp
  ring_nf
  simp only [neg_mul] at hcancel
  rw [hcancel]
  ring

/-- The usual derivative is the explicitly differentiated integral formula. -/
theorem deriv_cuspGreenSolutionFormula
    (t₀ T : ℝ) {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ}
    (hf : Continuous f) (t : ℝ) :
    deriv (cuspGreenSolutionFormula t₀ T κ f) t =
      cuspGreenSolutionFormulaDeriv t₀ T κ f t :=
  (hasDerivAt_cuspGreenSolutionFormula t₀ T hκ hf t).deriv

/-- A derivative certificate for the actual derivative of the integral formula. -/
theorem hasDerivAt_deriv_cuspGreenSolutionFormula
    (t₀ T : ℝ) {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ}
    (hf : Continuous f) (t : ℝ) :
    HasDerivAt (deriv (cuspGreenSolutionFormula t₀ T κ f))
      (κ ^ 2 * cuspGreenSolutionFormula t₀ T κ f t - f t) t := by
  have hfun : deriv (cuspGreenSolutionFormula t₀ T κ f) =
      cuspGreenSolutionFormulaDeriv t₀ T κ f :=
    funext (deriv_cuspGreenSolutionFormula t₀ T hκ hf)
  rw [hfun]
  exact hasDerivAt_cuspGreenSolutionFormulaDeriv t₀ T hf t

/-- The explicit finite-integral function solves the forced scalar equation. -/
theorem cuspGreenSolutionFormula_forcedODE
    (t₀ T : ℝ) {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ}
    (hf : Continuous f) (t : ℝ) :
    -deriv (deriv (cuspGreenSolutionFormula t₀ T κ f)) t +
      κ ^ 2 * cuspGreenSolutionFormula t₀ T κ f t = f t := by
  rw [(hasDerivAt_deriv_cuspGreenSolutionFormula t₀ T hκ hf t).deriv]
  ring

end GapFamily.Analytic
