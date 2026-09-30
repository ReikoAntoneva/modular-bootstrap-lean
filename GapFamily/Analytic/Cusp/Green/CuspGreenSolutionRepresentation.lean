import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionBasic
import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionFormula

/-!
# Identification of the actual Green integral with its finite formula

Splitting the ordinary integral at the observation point accounts for the
kernel's derivative jump without differentiating a totalized integral.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

private theorem cuspGreen_source_left (t₀ t u : ℝ) {κ : ℂ} (hκ : κ ≠ 0)
    (hu : u ≤ t) (z : ℂ) :
    cuspGreen t₀ t u κ * z =
      (Complex.exp (-κ * t) * (Complex.exp (κ * u) * z) -
        Complex.exp (-κ * ((t : ℂ) - 2*t₀)) * (Complex.exp (-κ * u) * z)) /
        (2*κ) := by
  rw [cuspGreen_eq_quotient t₀ t u hκ, abs_of_nonneg (sub_nonneg.mpr hu)]
  push_cast
  rw [show -κ * ((t : ℂ)-u) = -κ*t+κ*u by ring,
    show -κ * ((t : ℂ)+u-2*t₀) = -κ*((t : ℂ)-2*t₀)+ -κ*u by ring,
    Complex.exp_add, Complex.exp_add]
  ring

private theorem cuspGreen_source_right (t₀ t u : ℝ) {κ : ℂ} (hκ : κ ≠ 0)
    (hu : t ≤ u) (z : ℂ) :
    cuspGreen t₀ t u κ * z =
      (Complex.exp (κ * t) * (Complex.exp (-κ * u) * z) -
        Complex.exp (-κ * ((t : ℂ) - 2*t₀)) * (Complex.exp (-κ * u) * z)) /
        (2*κ) := by
  rw [cuspGreen_eq_quotient t₀ t u hκ, abs_of_nonpos (sub_nonpos.mpr hu)]
  push_cast
  rw [show -κ * (-((t : ℂ)-u)) = κ*t+ -κ*u by ring,
    show -κ * ((t : ℂ)+u-2*t₀) = -κ*((t : ℂ)-2*t₀)+ -κ*u by ring,
    Complex.exp_add, Complex.exp_add]
  ring

/-- On a physical interval below an actual source cutoff, the two formulas agree. -/
theorem cuspGreenSolution_eq_formula (t₀ T t : ℝ) (ht₀ : t₀ ≤ t) (htT : t ≤ T)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hf : Continuous f)
    (hfT : ∀ u, T < u → f u = 0) :
    cuspGreenSolution t₀ κ f t = cuspGreenSolutionFormula t₀ T κ f t := by
  have hp : Continuous (fun u : ℝ => Complex.exp (κ * u) * f u) := by fun_prop
  have hm : Continuous (fun u : ℝ => Complex.exp (-κ * u) * f u) := by fun_prop
  have hk : Continuous (fun u : ℝ => cuspGreen t₀ t u κ * f u) :=
    (cuspGreen_continuous_source t₀ t κ).mul hf
  have hleft :
      (∫ u in t₀..t, cuspGreen t₀ t u κ * f u) =
      (Complex.exp (-κ * t) * (∫ u in t₀..t, Complex.exp (κ * u) * f u) -
        Complex.exp (-κ * ((t : ℂ)-2*t₀)) *
          (∫ u in t₀..t, Complex.exp (-κ * u) * f u)) / (2*κ) := by
    calc
      _ = ∫ u in t₀..t,
          (Complex.exp (-κ * t) * (Complex.exp (κ * u) * f u) -
            Complex.exp (-κ * ((t : ℂ)-2*t₀)) *
              (Complex.exp (-κ * u) * f u)) / (2*κ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le ht₀] at hu
        exact cuspGreen_source_left t₀ t u hκ hu.2 (f u)
      _ = _ := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_sub
            ((hp.const_mul _).intervalIntegrable _ _) ((hm.const_mul _).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hright :
      (∫ u in t..T, cuspGreen t₀ t u κ * f u) =
      (Complex.exp (κ * t) * (∫ u in t..T, Complex.exp (-κ * u) * f u) -
        Complex.exp (-κ * ((t : ℂ)-2*t₀)) *
          (∫ u in t..T, Complex.exp (-κ * u) * f u)) / (2*κ) := by
    calc
      _ = ∫ u in t..T,
          (Complex.exp (κ * t) * (Complex.exp (-κ * u) * f u) -
            Complex.exp (-κ * ((t : ℂ)-2*t₀)) *
              (Complex.exp (-κ * u) * f u)) / (2*κ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le htT] at hu
        exact cuspGreen_source_right t₀ t u hκ hu.1 (f u)
      _ = _ := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_sub
            ((hm.const_mul _).intervalIntegrable _ _) ((hm.const_mul _).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [cuspGreenSolution_eq_interval t₀ T t (ht₀.trans htT) κ hfT,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hk.intervalIntegrable t₀ t) (hk.intervalIntegrable t T), hleft, hright]
  unfold cuspGreenSolutionFormula
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hm.intervalIntegrable t₀ t) (hm.intervalIntegrable t T)]
  ring

end GapFamily.Analytic
