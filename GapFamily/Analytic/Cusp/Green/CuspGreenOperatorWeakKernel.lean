import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorBasic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The actual scalar Green identity on a finite collar

Two ordinary fundamental-theorem-of-calculus identities and the actual slope
jump establish the test identity, including the threshold parameter and both
source endpoints. No distributional equation is taken as an input.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

theorem continuous_cuspGreen_test_integrand (a u : ℝ) (κ : ℂ)
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (fun t : ℝ =>
      cuspGreen a t u κ * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) := by
  have hG : Continuous (fun t : ℝ => cuspGreen a t u κ) :=
    (continuous_cuspGreen_position a κ).comp (continuous_id.prodMk continuous_const)
  have hψ' : ContDiff ℝ 1 (deriv ψ) := hψ.deriv'
  exact hG.mul (hψ'.continuous_deriv_one.neg.add
    (continuous_const.mul hψ.continuous))

/-- The full finite-interval boundary formula, proved from the literal Green kernel. -/
theorem cuspGreen_test_integral_boundary (a b u : ℝ) (hu : u ∈ Icc a b) (κ : ℂ)
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) :
    (∫ t : ℝ in a..b,
      cuspGreen a t u κ * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) =
      ψ u + cuspGreenRightSlope a b u κ * ψ b - cuspGreen a b u κ * deriv ψ b -
        cuspGreenLeftSlope a a u κ * ψ a := by
  have hG : Continuous (fun t : ℝ => cuspGreen a t u κ) :=
    (continuous_cuspGreen_position a κ).comp (continuous_id.prodMk continuous_const)
  have hL : Continuous (fun t : ℝ => cuspGreenLeftSlope a t u κ) := by
    unfold cuspGreenLeftSlope
    fun_prop
  have hR : Continuous (fun t : ℝ => cuspGreenRightSlope a t u κ) := by
    unfold cuspGreenRightSlope
    fun_prop
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hψdd : Differentiable ℝ (deriv ψ) := hψ.differentiable_deriv_two
  have hψdc : Continuous (deriv ψ) := hψ.continuous_deriv (by norm_num)
  have hc := continuous_cuspGreen_test_integrand a u κ hψ
  have hleft : (∫ t : ℝ in a..u,
      cuspGreen a t u κ * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) =
      (cuspGreenLeftSlope a u u κ * ψ u - cuspGreen a u u κ * deriv ψ u) -
        (cuspGreenLeftSlope a a u κ * ψ a - cuspGreen a a u κ * deriv ψ a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu.1
      ((hL.mul hψ.continuous).sub (hG.mul hψdc)).continuousOn
      _ (hc.intervalIntegrable a u)
    intro t ht
    apply (((cuspGreenLeftSlope_hasDerivAt a t u ht.2.le κ).mul
      (hψd t).hasDerivAt).sub ((cuspGreen_hasDerivAt_left a t u ht.2 κ).mul
      (hψdd t).hasDerivAt)).congr_deriv
    ring
  have hright : (∫ t : ℝ in u..b,
      cuspGreen a t u κ * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) =
      (cuspGreenRightSlope a b u κ * ψ b - cuspGreen a b u κ * deriv ψ b) -
        (cuspGreenRightSlope a u u κ * ψ u - cuspGreen a u u κ * deriv ψ u) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu.2
      ((hR.mul hψ.continuous).sub (hG.mul hψdc)).continuousOn
      _ (hc.intervalIntegrable u b)
    intro t ht
    apply (((cuspGreenRightSlope_hasDerivAt a t u ht.1.le κ).mul
      (hψd t).hasDerivAt).sub ((cuspGreen_hasDerivAt_right a t u ht.1 κ).mul
      (hψdd t).hasDerivAt)).congr_deriv
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a u) (hc.intervalIntegrable u b), hleft, hright,
    cuspGreen_boundary_left a u hu.1 κ, zero_mul, sub_zero]
  have hjump := cuspGreen_derivative_jump a u κ
  linear_combination -(ψ u) * hjump

/-- A clamped upper test and a Dirichlet lower test reproduce its value at every
source point. The lower derivative need not vanish because the kernel does. -/
theorem cuspGreen_test_integral (a b u : ℝ) (hu : u ∈ Icc a b) (κ : ℂ)
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ)
    (hψa : ψ a = 0) (hψb : ψ b = 0) (hψ'b : deriv ψ b = 0) :
    (∫ t : ℝ in a..b,
      cuspGreen a t u κ * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) = ψ u := by
  rw [cuspGreen_test_integral_boundary a b u hu κ hψ, hψa, hψb, hψ'b]
  ring

end GapFamily.Analytic
