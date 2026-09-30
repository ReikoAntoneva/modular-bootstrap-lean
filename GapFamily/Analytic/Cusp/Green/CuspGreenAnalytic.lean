import GapFamily.Analytic.Cusp.Green.CuspGreenBasic
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Entire dependence of the scalar cusp Green kernel

The ordinary finite integral agrees with the removable divided difference of its
exponential numerator. Thus its parameter dependence is entire, including at the
threshold. No assertion about an automorphic resolvent is made here.
-/

noncomputable section

namespace GapFamily.Analytic

open Filter Set
open scoped Topology

/-- The actual finite integral is the removable divided difference of its numerator. -/
theorem cuspGreen_eq_dslope (t₀ t u : ℝ) (κ : ℂ) :
    cuspGreen t₀ t u κ =
      dslope (fun z : ℂ => Complex.exp (-z * (|t-u| : ℝ)) -
        Complex.exp (-z * ((t+u-2*t₀ : ℝ) : ℂ))) 0 κ / 2 := by
  by_cases hκ : κ = 0
  · subst κ
    have hd : HasDerivAt
        (fun z : ℂ => Complex.exp (-z * (|t-u| : ℝ)) -
          Complex.exp (-z * ((t+u-2*t₀ : ℝ) : ℂ)))
        (-((|t-u| : ℝ) : ℂ) + ((t+u-2*t₀ : ℝ) : ℂ)) 0 := by
      convert (((hasDerivAt_id (0 : ℂ)).neg.mul_const (|t-u| : ℝ)).cexp.sub
        (((hasDerivAt_id (0 : ℂ)).neg.mul_const ((t+u-2*t₀ : ℝ) : ℂ)).cexp)) using 1 <;>
        simp <;> first | rfl | ring
    rw [cuspGreen_zero, dslope_same, hd.deriv]
    rcases le_total t u with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      push_cast
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      push_cast
      ring
  · rw [cuspGreen_eq_quotient t₀ t u hκ, dslope_of_ne _ hκ, slope_def_field]
    simp only [neg_zero, zero_mul, Complex.exp_zero, sub_self, sub_zero]
    ring

/-- Complex differentiability at every parameter, including the threshold. -/
theorem cuspGreen_differentiable (t₀ t u : ℝ) :
    Differentiable ℂ (cuspGreen t₀ t u) := by
  have hf : Differentiable ℂ (fun z : ℂ => Complex.exp (-z * (|t-u| : ℝ)) -
      Complex.exp (-z * ((t+u-2*t₀ : ℝ) : ℂ))) := by fun_prop
  have hs : Differentiable ℂ (dslope
      (fun z : ℂ => Complex.exp (-z * (|t-u| : ℝ)) -
        Complex.exp (-z * ((t+u-2*t₀ : ℝ) : ℂ))) 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (c := 0) univ_mem).mpr
      hf.differentiableOn)
  simpa only [← cuspGreen_eq_dslope] using hs.div_const (2 : ℂ)

/-- The scalar cusp Green kernel is entire in the spectral parameter. -/
theorem cuspGreen_analyticAt (t₀ t u : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (cuspGreen t₀ t u) κ :=
  (cuspGreen_differentiable t₀ t u).analyticAt κ

/-- Continuity uses the actual removable integral value. -/
theorem cuspGreen_continuous (t₀ t u : ℝ) : Continuous (cuspGreen t₀ t u) :=
  (cuspGreen_differentiable t₀ t u).continuous

/-- The complex threshold limit is `min(t,u)-t₀`. -/
theorem cuspGreen_tendsto_zero (t₀ t u : ℝ) :
    Tendsto (cuspGreen t₀ t u) (𝓝 (0 : ℂ)) (𝓝 ((min t u - t₀ : ℝ) : ℂ)) := by
  rw [← cuspGreen_zero t₀ t u]
  exact (cuspGreen_continuous t₀ t u).continuousAt

end GapFamily.Analytic
